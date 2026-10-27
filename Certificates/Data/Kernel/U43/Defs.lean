module

public import Certificates.Data.Kernel.Misc.PermG2U
public import Certificates.Data.Kernel.G2Three.Defs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43PairCheck
public import Mathlib

public section

namespace CFSG.KD.U43

open CFSG.KC.Loop CFSG.KC.Misc.G2U CFSG.RankThree.PartTwo.Sec4.Item434RemU43

@[expose] noncomputable def e4 (x k : Nat) : Nat := fldN x (Nat.mul 4 k) 4

@[expose] noncomputable def ent4 (x y i j : Nat) : Nat :=
  addC (addC (addC (mulC (e4 x (Nat.mul 4 i)) (e4 y j))
    (mulC (e4 x (Nat.add (Nat.mul 4 i) 1)) (e4 y (Nat.add 4 j))))
    (mulC (e4 x (Nat.add (Nat.mul 4 i) 2)) (e4 y (Nat.add 8 j))))
    (mulC (e4 x (Nat.add (Nat.mul 4 i) 3)) (e4 y (Nat.add 12 j)))

@[expose] noncomputable def M4 (x y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (ent4 x y (Nat.div k 4) (Nat.mod k 4))
      (Nat.mul 4 k))) 16

@[expose] def ONE4 : Nat := 3458767812358569987

@[expose] noncomputable def letP (A : Nat → Nat) (l : Nat) : Nat :=
  cond (Nat.blt l 3) (A l) (A 3)

@[expose] noncomputable def wordP (A : Nat → Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc l => M4 acc (letP A l)) ONE4

@[expose] noncomputable def lettersK (A : Nat → Nat) : Bool :=
  allBelow 4 1 fun s => Nat.beq (codes9 (letterCode s)) (A s)

@[expose] noncomputable def parK (X G : Nat → Nat) (K : Nat) (par : List (Nat × Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun ps _ ih i => bAnd(Nat.ble ps.1 i && Nat.blt ps.2 K &&
      Nat.beq (X (Nat.succ i)) (M4 (X ps.1) (G ps.2)), ih (Nat.succ i))) par

@[expose] noncomputable def closeU (X G POS : Nat → Nat) (n k hi : Nat) : Bool :=
  allBelow (Nat.mul n k) hi fun i =>
    Nat.blt (POS i) n && Nat.beq (X (POS i)) (M4 (X (Nat.div i k)) (G (Nat.mod i k)))

@[expose] noncomputable def okc (X : Nat → Nat) (w C : Nat) : Bool :=
  Nat.beq C ONE4 || (Nat.blt w 729 && Nat.beq (X w) C && Nat.beq (kindAt w) 3)

@[expose] noncomputable def e9K (X KW : Nat → Nat) (a b o : Nat) : Bool :=
  okc X (KW o) (M4 ONE4 ONE4) && okc X (KW (Nat.add o 1)) (M4 ONE4 b) &&
  okc X (KW (Nat.add o 2)) (M4 ONE4 (M4 b b)) &&
  okc X (KW (Nat.add o 3)) (M4 a ONE4) && okc X (KW (Nat.add o 4)) (M4 a b) &&
  okc X (KW (Nat.add o 5)) (M4 a (M4 b b)) &&
  okc X (KW (Nat.add o 6)) (M4 (M4 a a) ONE4) && okc X (KW (Nat.add o 7)) (M4 (M4 a a) b) &&
  okc X (KW (Nat.add o 8)) (M4 (M4 a a) (M4 b b))

@[expose] noncomputable def badPK (X KW : Nat → Nat) (o a b ra rb z WP WI : Nat) : Bool :=
  Nat.beq (M4 a b) (M4 b a) && Nat.beq (M4 a (M4 a a)) ONE4 && Nat.beq (M4 b (M4 b b)) ONE4 &&
  !(Nat.beq a ONE4) && !(Nat.beq b ONE4 || Nat.beq b a || Nat.beq b (M4 a a)) &&
  e9K X KW a b o &&
  Nat.beq (M4 (M4 WP a) WI) ra && Nat.beq (M4 (M4 WP b) WI) rb &&
  (Nat.beq (M4 (M4 WP z) WI) z || Nat.beq (M4 (M4 WP z) WI) (M4 z z))

@[expose] def badDK (k : Nat) : Bool :=
  (badTriple k).length == 3 && (badTriple k).all (· < 729) && (badTriple k).getD 0 0 == uZ &&
  repIdx (badClass k) < 12 && wordOK (badWord k)

@[expose] noncomputable def badK (X A KW : Nat → Nat) (k : Nat) : Bool :=
  badDK k && badPK X KW (Nat.mul 9 k) (X ((badTriple k).getD 1 0)) (X ((badTriple k).getD 2 0))
    (X ((badTriple (repIdx (badClass k))).getD 1 0))
    (X ((badTriple (repIdx (badClass k))).getD 2 0))
    (X uZ) (wordP A (badWord k)) (wordP A (invWord (badWord k)))

end CFSG.KD.U43

end
