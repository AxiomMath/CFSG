module

public import Certificates.Data.Kernel.O8.SBCenU

public section

namespace CFSG.KC.SBCenV

open CFSG.KC.Enum CFSG.KC.SBCen CFSG.KC.SBCenL CFSG.KC.SBCenU

@[expose] noncomputable def linLn (R X n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.xor ih
    (Nat.mul (Nat.land (Nat.shiftRight X i) RU) fld(R, Nat.mul 7 (Nat.shiftLeft 1 i), 127))) n

@[expose] noncomputable def linL (R X : Nat) : Nat := linLn R X 7

@[expose] noncomputable def linOK (R : Nat) : Bool := Nat.beq (linL R IDX) R

@[expose] noncomputable def memN (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun w _ ih => bIf(Nat.beq x w, true, ih)) L

@[expose] noncomputable def covK (F : Nat → Nat) (Om : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun e ih => bAnd(memN (Nat.shiftRight (F e) 7) Om, ih)) 128

@[expose] noncomputable def fibI (AR MR : Nat → Nat) (A M Y c z it : Nat) : Nat :=
  strictN (Nat.land it 511) fun w => strictN (Nat.shiftRight it 9) fun Mk =>
  strictN fld(MR w, Nat.mul 9 (Nat.shiftRight c 7), 511) fun h =>
  strictN fld(AR w, Nat.mul 7 (Nat.land c 127), 127) fun d => strictN fld(M, Nat.mul 9 h, 511) fun j =>
  strictN fld(MR j, Nat.mul 9 (Nat.shiftRight z 7), 511) fun p =>
  strictN (Nat.xor fld(A, Nat.mul 7 d, 127) fld(AR j, Nat.mul 7 (Nat.land z 127), 127)) fun k =>
    nIf(Nat.beq p 0, Nat.land Mk (zl (Nat.xor (Nat.xor IDX Y) (Nat.mul k RU))), 0)

@[expose] noncomputable def fibO (AR MR : Nat → Nat) (A M Y c z it : Nat) : Nat :=
  strictN (Nat.land it 511) fun w => strictN (Nat.shiftRight it 9) fun Mk =>
  strictN fld(MR w, Nat.mul 9 (Nat.shiftRight c 7), 511) fun h =>
  strictN fld(AR w, Nat.mul 7 (Nat.land c 127), 127) fun d => strictN fld(M, Nat.mul 9 h, 511) fun j =>
  strictN fld(MR j, Nat.mul 9 (Nat.shiftRight z 7), 511) fun p =>
  strictN (Nat.xor fld(A, Nat.mul 7 d, 127) fld(AR j, Nat.mul 7 (Nat.land z 127), 127)) fun k =>
    nIf(Nat.beq fld(MR p, Nat.mul 9 p, 511) 0,
      strictN (Nat.xor (Nat.xor IDX Y) (Nat.mul k RU)) fun X =>
      strictN (zl (Nat.xor X (linL (AR p) X))) fun Zl =>
      Nat.land Mk (nIf(Nat.beq p 0, Nat.xor Zl (Nat.land Zl (zl X)), Zl)), 0)

@[expose] noncomputable def unI (AR MR : Nat → Nat) (A M Y c z : Nat) (W : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun it _ ih => Nat.lor (fibI AR MR A M Y c z it) ih) W

@[expose] noncomputable def unO (AR MR : Nat → Nat) (A M Y c z : Nat) (W : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun it _ ih => Nat.lor (fibO AR MR A M Y c z it) ih) W

@[expose] noncomputable def grpW (mul : Nat → Nat → Nat) (AR MR F : Nat → Nat) (z P : Nat)
    (W Q U : List Nat) (nQ g : Nat) : Nat :=
  strictN (AR g) fun A => strictN (MR g) fun M => strictN (F (Nat.mul 128 g)) fun c =>
  strictN (linL A P) fun Y =>
  strictN (unI AR MR A M Y c z W) fun Zi => strictN (unO AR MR A M Y c z W) fun Zo =>
  Nat.add (pop Zi) (Nat.add (Nat.shiftLeft (qWalkU AR MR F A M g Zi Q) 20)
    (Nat.add (Nat.shiftLeft (cuSum (extMulF 65536 mul F z) (Nat.add g 512) Zi Q) 20)
      (Nat.shiftLeft (uWalkU AR MR F A M g Zo U) (Nat.mul 20 (Nat.succ nQ)))))

@[expose] noncomputable def fibOf (F : Nat → Nat) (w : Nat) : Nat :=
  Nat.add w (Nat.shiftLeft (lanesK (fun e => nIf(Nat.beq (Nat.shiftRight (F e) 7) w, 64, 0)) 128) 9)

@[expose] noncomputable def blkW (mul : Nat → Nat → Nat) (AR MR F : Nat → Nat) (z : Nat) (Om Q U : List Nat)
    (nQ t : Nat) : Nat :=
  strictN (lanesK (fun e => Nat.land (F e) 127) 128) fun P =>
  (fun W => Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.add (grpW mul AR MR F z P W Q U nQ (Nat.add (Nat.mul 64 t) j)) ih) 64)
    (List.rec (motive := fun _ => List Nat) [] (fun w _ ih => List.cons (fibOf F w) ih) Om)

end CFSG.KC.SBCenV

end
