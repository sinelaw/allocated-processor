{-# LANGUAGE RankNTypes, GADTs, NoMonomorphismRestriction, FlexibleContexts #-}
-- | 
-- Module      : Control.Processor
-- Copyright   : (c) Noam Lewis, 2010
-- License     : BSD3
--
-- Maintainer  : Noam Lewis <jones.noamle@gmail.com>
-- Stability   : experimental
-- Portability : tested on GHC only
--
-- Framework for expressing monadic actions that require initialization and finalization.
-- This module provides a /functional/ interface for defining and chaining a series of processors.
--
-- Motivating example: in the IO monad, bindings to C libraries that use functions such as: f(foo *src, foo
-- *dst), where the pointer `dst` must be pre-allocated. In this case we normally do:
--
--   > foo *dst = allocateFoo();
--   > ... 
--   > while (something) {
--   >    f(src, dst);
--   >    ...
--   > }
--   > releaseFoo(dst);
--
-- You can use the 'runUntil' function below to emulate that loop.
--
-- Processor is an instance of Category, Functor, Applicative and Arrow. 
--
-- In addition to the general type @'Processor' m a b@, this module also defines (and gives a semantic model
-- for) @'Processor' IO a b@, which has synonym @'IOProcessor' a b@.

module Control.Processor where

import Prelude hiding ((.),id)

import Control.Category
import Control.Applicative hiding (empty)
import Control.Arrow

import Control.Monad(liftM, join)

import Data.VectorSpace((^*), (*^), (^+^), (^-^), (^/), Scalar, VectorSpace, AdditiveGroup, zeroV)
import Data.Maybe(fromMaybe)

-- | The type of Processors
--
--    * @a@, @b@ = the input and output types of the processor (think a -> b)
--
--    * x = type of internal state (existentially quantified)
--
-- The arguments to the constructor are:
--
--    1. @a -> x ->m x@ - Processing function: Takes input and internal state, and returns new internal state.
--
--    2. @a -> m x@ - Allocator for internal state (this is run only once): Takes (usually the first) input, and returns initial internal state.
--
--    3. @x -> m b@ - Convertor from state x to output b: Takes internal state and returns the output.
--
--    4. @x -> m ()@ - Releaser for internal state (finalizer, run once): Run after processor is done being used, to release the internal state.
--
-- TODO: re-define in terms that don't need the @x@ existential (and the allocator), using a
-- continuation-style processing function.
--
data Processor m a b where
    Processor :: Monad m => (a -> x -> m x) -> (a -> m x) -> (x -> m b) -> (x -> m ()) -> (Processor m a b)
    
-- | The semantic model for 'IOProcessor' is a function:
--
-- > [[ 'IOProcessor' a b ]] = a -> b
--
-- To satisfy this model, the Processor value (the implementation) must obey the rules:
--
--    1. The processing function (@a -> x -> m x@) must act as if purely, so that indeed for a given input the
--       output is always the same. One particular thing to be careful with is that the output does not depend
--       on time (for example, you shouldn't use IOProcessor to implement an input device). The @IOSource@ type
--       is defined exactly for time-dependent processors. For pointer typed inputs and outputs, see next law.
--
--    2. For processors that work on pointers, @[[ Ptr t ]] = t@. This is guaranteed by the following
--       implementation constraints for @IOProcessor a b@:
--
--       1. If @a@ is a pointer type (@a = Ptr p@), then the processor must NOT write (modify) the referenced data.
--
--       2. If @b@ is a pointer, the memory it points to (and its allocation status) is only allowed to change
--          by the processor that created it (in the processing and releasing functions). In a way this
--          generalizes the first constraint.
--
-- Note, that unlike "Yampa", this model does not allow transformations of the type @(Time -> a) -> (Time ->
-- b)@. The reason is that I want to prevent arbitrary time access (whether causal or not). This limitation
-- means that everything is essentially "point-wise" in time. To allow memory-full operations under this
-- model, 'scanlT' is defined. See <http://www.ee.bgu.ac.il/~noamle/_downloads/gaccum.pdf> for more about
-- arbitrary time access.
type IOProcessor a b = Processor IO a b

-- | @'IOSource' a b@ is the type of time-dependent processors, such that:
--
-- > [[ 'IOSource' a b ]] = (a, Time) -> b
--
-- Thus, it is ok to implement a processing action that outputs arbitrary time-dependent values during runtime
-- regardless of input. (Although the more useful case is to calculate something from the input @a@ that is
-- also time-dependent. The @a@ input is often not required and in those cases @a = ()@ is used.
--
-- Notice that this means that IOSource doesn't qualify as an 'IOProcessor'. However, currently the
-- implementation /does NOT/ enforce this, i.e. IOSource is not a newtype; I don't know how to implement it
-- correctly. Also, one question is whether primitives like "chain" will have to disallow placing 'IOSource'
-- as the second element in a chain. Maybe they should, maybe they shouldn't.
type IOSource a b = Processor IO a b

-- | TODO: What's the semantic model for @'IOSink' a@?
type IOSink a = IOProcessor a ()

-- | TODO: do we need this? we're exporting the data constructor anyway for now, so maybe we don't.
processor :: Monad m =>
             (a -> x -> m x) -> (a -> m x) -> (x -> m b) -> (x -> m ())
          -> Processor m a b
processor = Processor

-- | Chains two processors serially, so one feeds the next.
chain :: Processor m a b'  -> Processor m b' b -> Processor m a b
chain (Processor pf1 af1 cf1 rf1) (Processor pf2 af2 cf2 rf2) = processor pf3 af3 cf3 rf3
    where pf3 a (x1,x2) = do
            x1' <- pf1 a x1
            b'  <- cf1 x1
            x2' <- pf2 b' x2
            return (x1', x2')
            
          af3 a = do
            x1 <- af1 a
            b' <- cf1 x1
            x2 <- af2 b'
            return (x1,x2)
            
          cf3 (_,x2) = cf2 x2
            
          rf3 (x1,x2) = do
            rf2 x2
            rf1 x1
  
-- | A processor that represents two sub-processors in parallel (although the current implementation runs them
-- sequentially, but that may change in the future)
parallel :: Processor m a b -> Processor m c d -> Processor m (a,c) (b,d)
parallel (Processor pf1 af1 cf1 rf1) (Processor pf2 af2 cf2 rf2) = processor pf3 af3 cf3 rf3
    where pf3 (a,c) (x1,x2) = do
            x1' <- pf1 a x1
            x2' <- pf2 c x2
            return (x1', x2')
            
          af3 (a,c) = do
            x1 <- af1 a
            x2 <- af2 c
            return (x1,x2)
            
          cf3 (x1,x2) = do
            b  <- cf1 x1
            d <- cf2 x2
            return (b,d)
            
          rf3 (x1,x2) = do
            rf2 x2
            rf1 x1

-- | Constructs a processor that: given two processors, gives source as input to both processors and runs them
-- independently, and after both have have finished, outputs their combined outputs.
-- 
-- Semantic meaning, using Arrow's (&&&) operator:
-- [[ forkJoin ]] = &&& 
-- Or, considering the Applicative instance of functions (which are the semantic meanings of a processor):
-- [[ forkJoin ]] = liftA2 (,)
-- Alternative implementation to consider: f &&& g = (,) <&> f <*> g
forkJoin :: Processor m a b  -> Processor m a b' -> Processor m a (b,b')
forkJoin (Processor pf1 af1 cf1 rf1) (Processor pf2 af2 cf2 rf2) = processor pf3 af3 cf3 rf3
    where --pf3 :: a -> (x1,x2) -> m (x1,x2)
          pf3 a (x1,x2) = do
            x1' <- pf1 a x1
            x2' <- pf2 a x2
            return (x1', x2')
            
          --af3 :: a -> m (x1, x2)
          af3 a = do
            x1 <- af1 a
            x2 <- af2 a
            return (x1,x2)
          
          --cf3 :: (x1,x2) -> m (b,b')
          cf3 (x1,x2) = do
            b <- cf1 x1
            b' <- cf2 x2
            return (b,b')
          
          --rf3 :: (x1,x2) -> m ()
          rf3 (x1,x2) = rf2 x2 >> rf1 x1


-------------------------------------------------------------
-- | The identity processor: output = input. Semantically, [[ empty ]] = id
empty :: Monad m => Processor m a a
empty = processor pf af cf rf
    where pf a _ = return a
          af   = return
          cf   = return
          rf _ = return ()
               
instance Monad m => Category (Processor m) where
  (.) = flip chain
  id  = empty
  
instance Monad m => Functor (Processor m a) where
  -- |
  -- > [[ fmap ]] = (.)
  --
  -- This could have used fmap internally as a Type Class Morphism, but monads
  -- don't neccesary implement the obvious: fmap = liftM.
  fmap f (Processor pf af cf rf) = processor pf af cf' rf
    where cf' x = liftM f (cf x) 

instance Monad m => Applicative (Processor m a) where
  -- | 
  -- > [[ pure ]] = const
  pure b = processor pf af cf rf
    where pf _ = return
          af _ = return ()
          cf _ = return b
          rf _ = return ()
            
  -- |
  -- [[ pf <*> px ]] = \a -> ([[ pf ]] a) ([[ px ]] a)
  -- (same as '(<*>)' on functions)
  (<*>) (Processor pf af cf rf) (Processor px ax cx rx) = processor py ay cy ry
    where py a (stateF, stateX) = do
            f' <- pf a stateF
            x' <- px a stateX
            return (f', x')
            
          ay a = do
            stateF <- af a
            stateX <- ax a
            return (stateF, stateX)
            
          -- this is the only part that seems specific to <*>
          cy (stateF, stateX) = do
            b2c <- cf stateF
            b <- cx stateX
            return (b2c b)
            
          ry (stateF, stateX) = do
            rx stateX
            rf stateF
  
-- | A few tricks by Saizan from #haskell to perhaps use here:
--  first f = (,) <$> (arr fst >>> f) <*> arr snd
--  arr f = f <$> id
--  f *** g = (arr fst >>> f) &&& (arr snd >>> g)
instance Monad m => Arrow (Processor m) where
  arr = flip liftA id
  (&&&) = forkJoin
  (***) = parallel
  first = (*** id)
  second = (id ***)
  

-------------------------------------------------------------

-- | Splits (duplicates) the output of a functor, or on this case a processor.
split :: Functor f => f a -> f (a,a)
split = (join (,) <$>)

-- | 'f --< g' means: split f and feed it into g. Useful for feeding parallelized (***'d) processors.
-- For example, a --< (b *** c) = a >>> (b &&& c)
(--<) :: (Functor (cat a), Category cat) => cat a a1 -> cat (a1, a1) c -> cat a c
f --< g = split f >>> g
infixr 1 --<


-------------------------------------------------------------
            
-- | Runs the processor once: allocates, processes, converts to output, and deallocates.
run :: Monad m => Processor m a b -> a -> m b
run = runWith id

-- | Keeps running the processing function in a loop until a predicate on the output is true.
-- Useful for processors whose main function is after the allocation and before deallocation.
runUntil :: Monad m => Processor m a b -> a -> (b -> m Bool) -> m b
runUntil (Processor pf af cf rf) a untilF = do
  x <- af a
  let repeatF y = do
        y' <- pf a y
        b <- cf y'
        b' <- untilF b
        if b' then return b else repeatF y'
  d <- repeatF x
  rf x
  return d


-- | Runs the processor once, but passes the processing + conversion action to the given function.
runWith :: Monad m => (m b -> m b') -> Processor m a b -> a -> m b'
runWith f (Processor pf af cf rf) a = do
        x <- af a
        b' <- f (pf a x >>= cf)
        rf x
        return b'


-------------------------------------------------------------
-- | Creates a processor that operates around an inner processor. 
--
-- Useful for sharing resources between two actions, a pre and a post action.
--        
-- The outer processor has /two/ processing functions, pre: @a->b@ and post: @c->d@. The last argument is the
-- inner processor, @Processor b c@.  Thus, the resulting processor takes the @a@, processes it into a @b@,
-- feeds that through the inner processor to get a @c@, and finally post-processes the @c@ into a @d@.
--
-- /Example scenario/: A singleton hardware device context, that cannot be duplicated or allocated more than
-- once. You need to both read and write to that device. It's not possible to create two processors, one for
-- reads and one for writes, because they need to use the same allocation (the device context). With
-- wrapPrcessor you can have the read as the pre-processing and write as the post-processing. Let's call the
-- result of calling wrapProcessor except the last argument, "myDeviceProcessor". Thus, you have:
--
-- >  [[ myDeviceProcessor innerProc ]] = read >>> innerProc >>> write
--
-- TODO: Find a more general / elegant solution to the "shared resource" problem.
wrapProcessor :: Monad m =>
                 (a -> x -> m x) -> (c -> x -> m x) -> 
                 (a -> m x) -> (x -> m b) -> (x -> m d) -> (x -> m ()) -> 
                 Processor m b c -> Processor m a d
wrapProcessor preProcF postProcF alloc preConv postConv release (Processor pf af cf rf) = processor procF allocF convF releaseF
    where procF a (x, innerX) = do
            x1 <- preProcF a x
            b  <- preConv x1
            innerX' <- pf b innerX
            c  <- cf innerX'
            x2 <- postProcF c x1
            return (x2, innerX')
          
          allocF a = do
            x <- alloc a
            b <- preConv x
            innerX <- af b
            return (x, innerX)
            
          convF (x, _) = postConv x

          releaseF (x, innerX) = do
            rf innerX
            release x
          
-------------------------------------------------------------

trace :: (Show a) => IOProcessor a a
trace = processor proc alloc conv release
    where proc a _ = do
            print a
            return a
          alloc a = do
            print $ "alloc: " ++ (show a)
            return a
          conv = return
          release _ = return ()


-------------------------------------------------------------
-- | scanlT provides the primitive for performing memory-full operations on time-dependent processors, as
-- | described in <http://www.ee.bgu.ac.il/~noamle/_downloads/gaccum.pdf>.
--
-- /Untested/, and also doesn't implement the "limit as dt -> 0" part of the model. Currently the precision of
-- the approximation is set by the samplerate (how many times per second the resulting processor is run, the
-- more the better for precision).
--
-- scanlT and all its uses are probably most (or only?) useful in the context of Processor IO. However for
-- generality it is defined here on arbitrary Processor m.
--
-- The @Processor m a b@ argument should really be time-dependent during runtime, so it's model can't be @a ->
-- b@. Thus it is most logical to use only 'IOSource' types for the processor argument.
scanlT :: (Monad m) => m t -> (b -> b -> t -> c -> c) -> c -> Processor m a b -> Processor m a c
scanlT clock transFunc initOut (Processor pf af cf rf) = processor procFunc allocFunc convFunc releaseFunc
    where procFunc curIn' (prevIn, prevOut, x) = do
            x' <- pf curIn' x
            curIn <- cf x'
            dtime <- clock
            let curOut = transFunc prevIn curIn dtime prevOut
            return (curIn, curOut, x')
          
          allocFunc firstIn' = do
            x <- af firstIn'
            firstIn <- cf x
            return (firstIn, initOut, x)
          
          convFunc (_, curOut, _) = return curOut
          
          releaseFunc (_, _, x') = rf x'
          
          
-- | Differentiate of time-dependent values, using 'scanlT'
differentiate :: (VectorSpace v, Fractional (Scalar v), Monad m) => m (Scalar v) -> Processor m a v -> Processor m a v
differentiate clock = scanlT clock diffFunc zeroV
    where diffFunc y' y dt _ = (y' ^-^ y) ^/ dt -- horrible approximation (unless sample rate is high)!
          
-- | Integration of time-dependent values, using 'scanlT', implemented by trapezoidal approximation.
integrate :: (VectorSpace v, Fractional (Scalar v), Monad m) => m (Scalar v) -> Processor m a v -> Processor m a v
integrate clock p = scanlT clock intFunc zeroV p
    where intFunc y' y dt prevSum = prevSum ^+^ (y' ^+^ y) ^* (dt / 2) -- horrible approximation!


-- -- | Convolution, using 'integrate'. 
--convolve :: (Monad m) => m (Scalar v) -> (Scalar v -> v) -> Processor m a v -> Processor m a v
--convolve clock convArg proc =


-- | Running maximum of a processor's values
maxP :: (Ord b, Monad m) => m t -> b -> Processor m a b -> Processor m a b
maxP clock minVal = scanlT clock maxFunc minVal
    where maxFunc _ y _ y' = max y' y
          
-- | Running minimum of a processor's values
minP :: (Ord b, Monad m) => m t -> b -> Processor m a b -> Processor m a b
minP clock maxVal = scanlT clock minFunc maxVal
    where minFunc _ y _ y' = min y' y



-- can only be defined for discrete time
-- t = the time steps
nStepsMemory :: (Monad m) => Int -> ([(t, b)] -> c) -> (t, b) -> c -> m t -> Processor m a b -> Processor m a c
nStepsMemory n f initA initB clock pIn = (scanlT clock f' (take n . repeat $ initA, initB) pIn) >>> arr snd
    where f' _ y2 dt (lastNSamps, _) = (nextSamps, f nextSamps )
              where nextSamps = (dt, y2) : (init lastNSamps)


-- | Holds a Maybe-valued processor and reports the time passed since last value was seen.
holdMaybe :: (Num t, Monad m) => b -> m t -> Processor m a (Maybe b) -> Processor m a (b, t)
holdMaybe initLast clock pIn = scanlT clock f' (initLast,0) pIn
    where f' _ y2 dt (last', timeMissing) = (fromMaybe last' y2, calcTimeMissing y2 timeMissing)
              where calcTimeMissing Nothing t = t + dt
                    calcTimeMissing _       _ = 0

-- | Given a 'holdMaybe'-type processor, reverts back to a default value if no input was 
-- seen for more than a given time limit
revertAfterT :: (Monad m, Ord t) => t -> b -> Processor m a (b, t) -> Processor m a b
revertAfterT maxT revertVal p = p >>> arr (\(b,t) -> if t > maxT then revertVal else b)

-- todo: this is a general function, perhaps move to a module?
discreteConv :: (VectorSpace a) => [Scalar a] -> [a] -> a
discreteConv weights samps = foldr (^+^) zeroV $ zipWith (*^) weights samps
          
-- | Finite impulse response
fir :: (Monad m, Fractional (Scalar v), VectorSpace v) => [Scalar v] -> t -> m t -> Processor m a v -> Processor m a v
fir weights initTimeStep clock pIn = nStepsMemory (length weights) (discreteConv weights . map snd) (initTimeStep, zeroV) zeroV clock pIn
