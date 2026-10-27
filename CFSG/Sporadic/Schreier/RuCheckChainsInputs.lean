module

public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Certificates.NativeSchreierCard
public meta import CFSG.Sporadic.Schreier.RuArrays
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruBaseArr (n : ℕ) (b : List ℕ) : Array ℕ := (b.map (· % n)).toArray

@[expose] def ruChainOK (n : ℕ) (S : Array (Array ℕ)) (k s : ℕ) (b : List ℕ)
    (D : List (List ℤ)) : Bool :=
  rawChainOK n (S.extract 0 k) S (ruBaseArr n b) (ruWordsArr k s D) 4

@[expose] def ruSift (n : ℕ) (S : Array (Array ℕ)) (b : List ℕ) (g : Array ℕ) : Bool :=
  siftA n (rawLevels n S (ruBaseArr n b)) (ruBaseArr n b) 0 g

end CFSG.Sporadic.RuSchreier
