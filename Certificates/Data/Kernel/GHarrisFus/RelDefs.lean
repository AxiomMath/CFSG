module

public import Certificates.Data.Kernel.GHarrisFus.Defs
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusCertInputs
public import Mathlib.Tactic.Ring

public section

open CFSG.ComponentClassification.GHarris.SCert

namespace CFSG.KC.GHFus

@[expose] def patB (x y : SE) : Nat :=
  (x * y == 1).toNat + 2 * ((x * y) * (x * y) == 1).toNat +
    4 * ((x * y) * (x * y) * ((x * y) * (x * y)) == 1).toNat + 8 * (x * y == y * x).toNat

@[expose] def testB (A : Fus.Data) (t : Test) : Bool :=
  t.1.all (fun i => i == 0 || i == 9 || i == 18) &&
    t.2.1.all (fun i => i == 0 || i == 9 || i == 18 || i == 27) &&
    ((((t.1 ++ t.2.1).foldl (fun k i => A.mi k (i / 9)) 0) == 0) == t.2.2)

@[expose] noncomputable def relB (A : Fus.Data) (D : FusT) : Bool :=
  (D.1 == A.target.enc) &&
    (List.range 6).all (fun k => nib D.2.1 k == patB (A.gens.getD ([0, 0, 1, 0, 1, 2].getD k 0) 1)
      (A.gens.getD ([1, 2, 2, 3, 3, 3].getD k 0) 1)) &&
    testB A D.2.2.1.1 && testB A D.2.2.1.2.1 && testB A D.2.2.1.2.2 &&
    (D.2.2.2.1 == ((List.range 32).filter fun k => Fus.isInv (· * ·) (A.elt (· * ·) k)).map
      (fun k => (9 * SE.clsTab (A.elt (· * ·) k), (A.words.getD k []).map (9 * ·)))) &&
    (List.range 9).all (fun i => (List.range 9).all fun j =>
      !D.2.2.2.2.1.testBit (9 * i + j) || A.badPairs.contains (i, j)) &&
    (D.2.2.2.2.2.1 ==
      (List.range 32).map (fun k => ((A.elt (· * ·) k).enc, (A.words.getD k []).map (9 * ·)))) &&
    (D.2.2.2.2.2.2.1 == (A.words.getD A.zIdx []).map (9 * ·)) &&
    (D.2.2.2.2.2.2.2.1 == A.useE) && (D.2.2.2.2.2.2.2.2 == A.useF)

end CFSG.KC.GHFus
