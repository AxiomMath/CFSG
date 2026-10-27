module

public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.CFSGNative.SectionRank.TitsLocal

public noncomputable section

namespace CFSG.KC.LocalComp.Tits

open CFSG.KC.Enum CFSG.KS CFSG.SectionRank.Native.Tits

@[expose] def mvK : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | c :: cs, v, i => Nat.xor (nIf(Nat.beq (Nat.land (Nat.shiftRight v i) 1) 1, c, 0)) (mvK cs v (i + 1))

@[expose] def colsK (gs : Array (List Nat)) (s : Nat) : List Nat := gs.toList.getD s []

@[expose] noncomputable def rf (R k : Nat) : Nat := pg 16 (mask 16) R k

@[expose] noncomputable def orbitK (gs : Array (List Nat)) (root cap N : Nat) (TP TG TR : Nat → Nat) :
    Bool :=
  bAnd(Nat.ble N cap, bAnd(Nat.blt 0 N,
  bAnd(allN N (fun i => Nat.blt (TP i) (Nat.shiftLeft 1 52)),
  bAnd(allN (N - 1) (fun i => Nat.blt (TP i) (TP (i + 1))),
  bAnd(allN gs.size (fun s => bAnd(Nat.beq (Nat.shiftRight (TG s) (Nat.mul N 11)) 0,
    allN N fun i => strictB (pg 11 (mask 11) (TG s) i) fun j =>
      bAnd(Nat.blt j N, Nat.beq (TP j) (mvK (colsK gs s) (TP i) 0)))),
  bAnd(Nat.beq (TP (rf (TR 0) 0)) root,
  bAnd(allN N (fun j => bAnd(Nat.blt (rf (TR j) 0) N,
    bIf(Nat.beq j 0, true, bAnd(Nat.blt (rf (TR j) 1) j, bAnd(Nat.blt (rf (TR j) 2) gs.size,
      Nat.beq (rf (TR j) 0) (pg 11 (mask 11) (TG (rf (TR j) 2)) (rf (TR (rf (TR j) 1)) 0))))))),
    Nat.beq (foldN N (fun j s => Nat.lor s (Nat.shiftLeft 1 (rf (TR j) 0))) 0)
      (Nat.sub (Nat.shiftLeft 1 N) 1))))))))

@[expose] def topK : Nat → Nat → Nat
  | 0, _ => 52
  | b + 1, v => nIf(Nat.beq (Nat.land (Nat.shiftRight v b) 1) 1, b, topK b v)

@[expose] def redK : List (Nat × Nat) → Nat → Nat
  | [], v => v
  | (b, p) :: ps, v => redK ps (nIf(Nat.beq (Nat.land (Nat.shiftRight v b) 1) 1, Nat.xor v p, v))

@[expose] def insK (b v : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(b, v)]
  | (c, p) :: ps => if c < b then (b, v) :: (c, p) :: ps else (c, p) :: insK b v ps

@[expose] def basisK (TP : Nat → Nat) : Nat → Nat → List (Nat × Nat) → List Nat → List Nat
  | 0, _, _, acc => acc
  | f + 1, i, ps, acc =>
    let v := redK ps (TP i)
    if v = 0 then basisK TP f (i + 1) ps acc
    else basisK TP f (i + 1) (insK (topK 52 v) v ps) (i :: acc)

@[expose] noncomputable def idxK (N : Nat) (TP : Nat → Nat) (v : Nat) : Nat :=
  foldN N (fun i s => nIf(Nat.beq (TP i) v, i, s)) N

@[expose] def checkK (N : Nat) (TP : Nat → Nat) (bv CP : List Nat) : Bool :=
  allN N (fun i => Nat.blt (TP i) (Nat.shiftLeft 1 52)) &&
    allN (N - 1) (fun i => Nat.blt (TP i) (TP (i + 1))) && CP.all (· < N) &&
    CP == (bv.map (idxK N TP) ++ (basisK TP N 0 [] []).reverse)

variable (n w : Nat)

@[expose] noncomputable def letK (TG : Nat → Nat) (z : Int) : Nat :=
  if 0 < z ∧ z ≤ 4 then TG (z.toNat - 1)
  else if z < 0 ∧ -z ≤ 4 then pinvS n w (mask w) (TG ((-z).toNat - 1))
  else pidn n w

@[expose] noncomputable def wordK (TG : Nat → Nat) : List Int → Nat
  | [] => pidn n w
  | z :: zs => strictN (wordK TG zs) fun t => pcomp n w (mask w) (letK n w TG z) t

@[expose] noncomputable def eqOnK (CP : List Nat) (A B : Nat) : Bool :=
  CP.all fun p => Nat.beq (pg w (mask w) A p) (pg w (mask w) B p)

@[expose] noncomputable def nfK (X Y Z i j k : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) (ppow n w (mask w) (pidn n w) X i)
    (ppow n w (mask w) (pidn n w) Y j)) (ppow n w (mask w) (pidn n w) Z k)

@[expose] noncomputable def keyK (CP : List Nat) (A : Nat) : Nat :=
  CP.foldr (fun p acc => Nat.add (pg w (mask w) A p) (Nat.mul 2048 acc)) 0

@[expose] noncomputable def keysK (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | u :: us => Nat.rec (motive := fun _ => List Nat) (0 :: keysK f us)
      (fun k _ => Nat.succ k :: keysK f us) (f u)

@[expose] def distinctK : List Nat → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !(Nat.beq x y)) && distinctK xs

@[expose] def lettersK (D : TitsWitness) : Bool :=
  (tLetters ()).toList.all isManifest && (D.wx ++ D.wy ++ D.wh).all (· < (tLetters ()).size)

@[expose] noncomputable def conjOnK (CP : List Nat) (X Y W : Nat) : Bool :=
  eqOnK w CP (pcomp n w (mask w) X Y) (pcomp n w (mask w) W X)

@[expose] noncomputable def cubicK (TG : Nat → Nat) (CP : List Nat) (D : TitsWitness) : Bool :=
  let m := mask w
  let idn := pidn n w
  let u := D.nums
  strictB (wordK n w TG (texpand D.wx)) fun X => strictB (wordK n w TG (texpand D.wy)) fun Y =>
  strictB (wordK n w TG (texpand D.wh)) fun H =>
  strictB (pinvS n w m X) fun XI => strictB (pinvS n w m Y) fun YI =>
  strictB (pcomp n w m (pcomp n w m (pcomp n w m X Y) XI) YI) fun Z =>
  lettersK D && Nat.beq u.length 7 &&
    allN 4 (fun s => permOK n w m (Nat.mul n w) (TG s) (pinvS n w m (TG s))) &&
    permOK n w m (Nat.mul n w) X XI &&
    permOK n w m (Nat.mul n w) Y YI &&
    eqOnK w CP (ppow n w m idn X 3) idn && eqOnK w CP (ppow n w m idn Y 3) idn &&
    !eqOnK w CP Z idn && eqOnK w CP (pcomp n w m Z X) (pcomp n w m X Z) &&
    eqOnK w CP (pcomp n w m Z Y) (pcomp n w m Y Z) &&
    distinctK (keysK (fun v => keyK w CP (nfK n w X Y Z (v % 3) (v / 3 % 3) (v / 9)))
      (List.range 27)) &&
    conjOnK n w CP H X (nfK n w X Y Z (u.getD 0 0) (u.getD 1 0) (u.getD 4 0)) &&
    conjOnK n w CP H Y (nfK n w X Y Z (u.getD 2 0) (u.getD 3 0) (u.getD 5 0)) &&
    conjOnK n w CP H Z (ppow n w m idn Z (u.getD 6 0))

@[expose] noncomputable def squareK (TG : Nat → Nat) (CP : List Nat) (D : TitsWitness) : Bool :=
  let m := mask w
  let idn := pidn n w
  let u := D.nums
  strictB (wordK n w TG (texpand D.wx)) fun X => strictB (wordK n w TG (texpand D.wy)) fun Y =>
  strictB (wordK n w TG (texpand D.wh)) fun H =>
  lettersK D && Nat.beq u.length 4 &&
    allN 4 (fun s => permOK n w m (Nat.mul n w) (TG s) (pinvS n w m (TG s))) &&
    eqOnK w CP (ppow n w m idn X 5) idn && eqOnK w CP (ppow n w m idn Y 5) idn &&
    eqOnK w CP (pcomp n w m X Y) (pcomp n w m Y X) &&
    distinctK (keysK (fun v => keyK w CP (nfK n w X Y idn (v % 5) (v / 5) 0)) (List.range 25)) &&
    conjOnK n w CP H X (nfK n w X Y idn (u.getD 0 0) (u.getD 2 0) 0) &&
    conjOnK n w CP H Y (nfK n w X Y idn (u.getD 1 0) (u.getD 3 0) 0)

end CFSG.KC.LocalComp.Tits

end
