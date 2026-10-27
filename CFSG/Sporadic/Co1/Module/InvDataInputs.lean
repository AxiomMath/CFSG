
module

public import CFSG.Sporadic.Co1.Module.FormsInputs
public import Certificates.Data.CFSGNative.Co1.Involutions

@[expose] public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative

set_option Elab.async false

@[expose] def invWord (s : String) : List Bool := s.toList.map (· == 'A')

@[expose] def kWord1 : List Bool := invWord "ABABABABABABABABABABABABABABABABABABABAB"

@[expose] def kWord2 : List Bool :=
  invWord (
    "BBBBABBBBABBBBAABABABBABBABABABBABBABABABBABBABABA" ++
    "BBABBABABABBABBABBABBABB")

@[expose] def nWord1 : List Bool := invWord "BBABBABBABBABBABBAABABBABABBABABBABABABABABAB"

@[expose] def nWord2 : List Bool :=
  invWord (
    "BBBBABBBBABBBBABBBBABBBBAABABABBABABABBABABABABBAB" ++
    "ABABBABABABABBABABABBABABABABBABABABBABABBABBABBAB" ++
    "BABB")

@[expose] def kGens : Array (Array ℕ) := #[wordRows kWord1, wordRows kWord2]

@[expose] def nGens : Array (Array ℕ) := #[wordRows nWord1, wordRows nWord2]

@[expose] def kGensInv : Array (Array ℕ) := kGens.map invRows

@[expose] def nGensInv : Array (Array ℕ) := nGens.map invRows

@[expose] def wordA : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1,
    0, 0, 0, 0]

@[expose] def wordB : List ℕ :=
  [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 1]

@[expose] def wordC : List ℕ := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def rowsSA : Array ℕ := powRows 24 (genWordRows kGens wordA) 7

@[expose] def rowsSB : Array ℕ := powRows 24 (genWordRows nGens wordB) 6

@[expose] def rowsSC : Array ℕ := powRows 24 (genWordRows nGens wordC) 5

@[expose] def code3 : ℕ := 14717452

@[expose] def code4 : ℕ := 10075731

@[expose] def repOK (G Gi : Array (Array ℕ)) (S : Array ℕ) (c : ℕ) : Bool :=
  G.size == 2 && Gi.size == 2 && orderIs S 2 && isFixedN (transposeRows 24 S) c &&
    (List.range 2).all fun l =>
      mulRows 24 G[l]! Gi[l]! == idRows 24 && isFixedN (transposeRows 24 G[l]!) c

@[expose] def countsOK (S : Array ℕ) (a b : ℕ) : Bool :=
  fixCount (transposeRows 24 S) == a &&
    fixCountQ (transposeRows 24 S) (transposeRows 24 qRows) == b

@[expose] def conjCheck (G Gi : Array (Array ℕ)) (S : Array ℕ) (n : ℕ) : Bool :=
  let c := conjBFS G Gi S n
  ctOK G Gi S c && decide (n ≤ c.pts.size)

@[expose] def witOK (w : List Bool) (S T : Array ℕ) (n : ℕ) : Bool :=
  mulRows 24 (wordRows w) (invRows (wordRows w)) == idRows 24 &&
    orderIs (mulRows 24 (mulRows 24 (mulRows 24 (wordRows w) S) (invRows (wordRows w))) T) n

end CFSG.Sporadic.Co1.Module
