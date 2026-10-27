module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Check

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

open CFSG.GammaU.Native

def hj_zWord : List Nat := hj_a1Words.get ⟨0, by decide⟩

def hj_b1Word : List Nat := hj_a1Words.get ⟨0, by decide⟩
def hj_b2Word : List Nat := hj_a1Words.get ⟨3, by decide⟩
def hj_g1Word : List Nat := hj_a1Words.get ⟨1, by decide⟩

def hj_c1Word : List Nat := hj_a2Words.get ⟨1, by decide⟩
def hj_c2Word : List Nat := hj_a2Words.get ⟨2, by decide⟩
def hj_h1Word : List Nat := hj_a2Words.get ⟨0, by decide⟩

def hjT1Gens (_ : Unit := ()) : List (Array Nat) :=
  hj_t0Words.map wordR ++ [hjTauc]

def hjT1Invs (_ : Unit := ()) : List (Array Nat) :=
  (enumGrp (hjT1Gens ())).filter isInvol

def hjT1Tab (_ : Unit := ()) : List (Array Nat × Nat) :=
  (hjT1Invs ()).map fun r => (r, (fixCodes r).length)

def hjLookup (tab : List (Array Nat × Nat)) (r : Array Nat) : Nat :=
  ((tab.find? fun p => p.1 == r).map fun p => p.2).getD 0

def hjZCheck (_ : Unit := ()) : Bool :=
  let z := wordR hj_zWord
  isInvol z && (fixCodes z).length == 256

def hjTripleRows (x y z : Array Nat) : List (Array Nat) :=
  [x, y, mulR x y, z, mulR z x, mulR z y, mulR (mulR x y) z]

def hjMixedSpan (tab : List (Array Nat × Nat)) (x y z : Array Nat) : Bool :=
  (hjTripleRows x y z).any (fun r => hjLookup tab r == 64) &&
    (hjTripleRows x y z).any (fun r => hjLookup tab r == 256)

def hjTripleOK (tab : List (Array Nat × Nat)) (x y z : Array Nat) : Bool :=
  x == y || x == z || y == z || !commR x y || !commR x z || !commR y z ||
    [idR, x, y, mulR x y].contains z || hjLookup tab x != hjLookup tab y ||
    hjLookup tab y != hjLookup tab z || hjMixedSpan tab x y z

def hjPureTripleCheck (_ : Unit := ()) : Bool :=
  let invs := hjT1Invs ()
  let tab := hjT1Tab ()
  invs.all fun x => invs.all fun y => invs.all fun z => hjTripleOK tab x y z

def hjE16A1Check (_ : Unit := ()) : Bool :=
  let b1 := wordR hj_b1Word
  let b2 := wordR hj_b2Word
  let g := wordR hj_g1Word
  isInvol b1 && isInvol b2 && b1 != b2 && commR b1 b2 &&
    appN b1 81 == 81 && appN b2 81 == 81 && appN g 81 != 81

def hjE16A2Check (_ : Unit := ()) : Bool :=
  let b1 := wordR hj_c1Word
  let b2 := wordR hj_c2Word
  let g := wordR hj_h1Word
  isInvol b1 && isInvol b2 && b1 != b2 && commR b1 b2 &&
    appN b1 136 == 136 && appN b2 136 == 136 && appN g 136 != 136

def hjThreeThreeCheck (_ : Unit := ()) : Bool :=
  hjZCheck () && (hjPureTripleCheck () && (hjE16A1Check () && hjE16A2Check ()))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

end
