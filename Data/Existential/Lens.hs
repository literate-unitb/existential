module Data.Existential.Lens where

import Control.Lens.Bound
import Data.Existential
import Data.Proxy

inside :: p => ExLens c p (Cell1 f c) (Cell1 g c) f g
inside = makeExLens insideAux

insideAux :: (Functor f,p)
          => Proxy p 
          -> ExLensType c p f (Cell1 g c) (Cell1 h c) g h
insideAux _ f (Cell x) = Cell <$> f x
