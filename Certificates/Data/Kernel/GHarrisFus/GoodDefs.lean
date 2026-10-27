module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusCertInputs
public import Mathlib.Tactic.Ring

public section

open CFSG.ComponentClassification.GHarris.SCert

namespace CFSG.KC.GHFus

@[expose] def ikB (A : Fus.Data) (IK : List (Nat × List Nat)) : Bool :=
  IK.all fun r => (List.range 32).any fun k =>
    r == (9 * SE.clsTab (A.elt (· * ·) k), (A.words.getD k []).map (9 * ·)) &&
      Fus.isInv (· * ·) (A.elt (· * ·) k)

@[expose] def wordsB (A : Fus.Data) (ks : List Nat) (ws : List (List Nat)) : Bool :=
  ws == ks.map fun k => (A.words.getD k []).map (9 * ·)

@[expose] def codesB (cs : List Nat) : Bool := cs.all fun c => (SE.dec c).enc == c

end CFSG.KC.GHFus
