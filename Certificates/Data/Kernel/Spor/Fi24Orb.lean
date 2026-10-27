module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Common.LceS
public import Certificates.Data.Kernel.Spor.Fi24FixK

public section

namespace CFSG.KC.Fi24Orb

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def tk (TG : Nat → Nat → Nat) (k p : Nat) : Nat :=
  TG (Nat.succ k) (TG (nat_lit 0) p)

@[expose] noncomputable def fPar (e : Nat) : Nat := Nat.land e (nat_lit 524287)

@[expose] noncomputable def fLab (e : Nat) : Nat := fld(e, nat_lit 19, nat_lit 15)

@[expose] noncomputable def fComp (e : Nat) : Nat := fld(e, nat_lit 23, nat_lit 3)

@[expose] noncomputable def fDep (e : Nat) : Nat := fld(e, nat_lit 25, nat_lit 127)

@[expose] noncomputable def fPos (e : Nat) : Nat := fld(e, nat_lit 32, nat_lit 65535)

@[expose] noncomputable def h0L (k : Nat) : Bool :=
  andB (Nat.blt k (nat_lit 10)) (bIf(Nat.beq k (nat_lit 8), false, true))

@[expose] noncomputable def forStep (FD S : Nat → Nat) (TG : Nat → Nat → Nat) (n s0 r1 r e : Nat) :
    Bool :=
  letB (fComp e) (fun c =>
  andB (orB (Nat.beq c (nat_lit 1)) (andB (Nat.beq c (nat_lit 2))
      (letB (fPos e) (fun q => andB (Nat.blt q (nat_lit 31671)) (Nat.beq (S q) r)))))
    (letB (fDep e) (fun d => bIf(Nat.beq d (nat_lit 0),
      orB (andB (Nat.beq r s0) (Nat.beq c (nat_lit 2))) (andB (Nat.beq r r1) (Nat.beq c (nat_lit 1))),
      letB (fPar e) (fun p => andB (Nat.ble (nat_lit 1) p) (andB (Nat.blt p n)
        (letB (FD p) (fun e' => andB (Nat.beq (Nat.succ (fDep e')) d) (andB (Nat.beq (fComp e') c)
          (letB (fLab e) (fun k => andB (h0L k) (Nat.beq (tk TG k p) r))))))))))))

@[expose] noncomputable def forOK (FD S : Nat → Nat) (TG : Nat → Nat → Nat) (n s0 r1 lo : Nat) :
    Bool :=
  allBelow (nat_lit 1024) (nat_lit 16) (fun t => letB (Nat.add lo t) (fun r =>
    bIf(andB (Nat.ble (nat_lit 1) r) (Nat.blt r n), letB (FD r) (fun e => forStep FD S TG n s0 r1 r e),
      true)))

@[expose] noncomputable def inSOK (FD S : Nat → Nat) (m lo : Nat) : Bool :=
  allBelow (nat_lit 4096) (nat_lit 64) (fun t => letB (Nat.add lo t) (fun j =>
    bIf(Nat.blt j m, Nat.beq (fComp (FD (S j))) (nat_lit 2), true)))

@[expose] noncomputable def vtOK (VT : Nat → Nat) (TG : Nat → Nat → Nat) (VW : List Nat) (n lo : Nat) :
    Bool :=
  allBelow (nat_lit 512) (nat_lit 8) (fun t => letB (Nat.add lo t) (fun r =>
    bIf(Nat.blt r n, Nat.beq (walk TG VW r) (VT r), true)))

@[expose] noncomputable def vt7 (VT : Nat → Nat) (r : Nat) : Nat :=
  strictN (VT r) (fun r1 => strictN (VT r1) (fun r2 => strictN (VT r2) (fun r3 =>
    strictN (VT r3) (fun r4 => strictN (VT r4) (fun r5 => strictN (VT r5) (fun r6 => VT r6))))))

@[expose] noncomputable def oA (e : Nat) : Nat := Nat.land e (nat_lit 524287)

@[expose] noncomputable def oB (e : Nat) : Nat := fld(e, nat_lit 19, nat_lit 524287)

@[expose] noncomputable def oPar (e : Nat) : Nat := fld(e, nat_lit 38, nat_lit 524287)

@[expose] noncomputable def oLab (e : Nat) : Nat := fld(e, nat_lit 57, nat_lit 3)

@[expose] noncomputable def treeStep (OL : Nat → Nat) (k e : Nat) : Bool :=
  letB (oPar e) (fun p => andB (Nat.blt p k) (letB (OL p) (fun ep => letB (oLab e) (fun l =>
    orB (andB (Nat.beq l (nat_lit 1)) (Nat.beq (oA ep) k))
      (andB (Nat.beq l (nat_lit 2)) (Nat.beq (oB ep) k))))))

@[expose] noncomputable def bindStep (OL NM NI VT : Nat → Nat) (TG : Nat → Nat → Nat) (AW : List Nat)
    (n k : Nat) : Bool :=
  letB (NM k) (fun r => andB (Nat.blt r n) (andB (Nat.beq (NI r) k)
    (letB (OL k) (fun e =>
      andB (letB (oA e) (fun a => andB (Nat.blt a n) (andB (Nat.beq (oA (OL a)) k)
        (Nat.beq (NM a) (walk TG AW r)))))
      (andB (letB (oB e) (fun b => andB (Nat.blt b n) (andB (Nat.beq (oB (OL (oB (OL b)))) k)
        (Nat.beq (NM b) (vt7 VT r)))))
      (orB (Nat.beq k (nat_lit 0)) (treeStep OL k e)))))))

@[expose] noncomputable def bindOK (OL NM NI VT : Nat → Nat) (TG : Nat → Nat → Nat) (AW : List Nat)
    (n lo : Nat) : Bool :=
  allBelow (nat_lit 512) (nat_lit 8) (fun t => letB (Nat.add lo t) (fun k =>
    bIf(Nat.blt k n, bindStep OL NM NI VT TG AW n k, true)))

@[expose] def segW (w : List Nat) (lo len : Nat) : List Nat := List.take len (List.drop lo w)

@[expose] noncomputable def M253 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 253)) (nat_lit 1)

@[expose] noncomputable def agreeRow (Y C i : Nat) : Bool :=
  andB (Nat.beq (Nat.land (Nat.shiftRight Y (Nat.mul (nat_lit 781) i)) M253)
      (Nat.land (Nat.shiftRight C (Nat.mul (nat_lit 253) i)) M253))
    (Nat.beq (Nat.land (Nat.shiftRight Y (Nat.add (nat_lit 609961) (Nat.mul (nat_lit 781) i))) M253)
      (Nat.land (Nat.shiftRight C (Nat.add (nat_lit 64009) (Nat.mul (nat_lit 253) i))) M253))

@[expose] noncomputable def agreeOK (Y C : Nat) : Bool :=
  allBelow (nat_lit 253) (nat_lit 4) (fun i => agreeRow Y C i)

@[expose] noncomputable def slpStep (mul : Nat → Nat → Nat) (vld : Nat → Bool) (RS IJ : Nat → Nat)
    (k : Nat) : Bool :=
  andB (vld (RS k)) (orB (Nat.blt k (nat_lit 2)) (letB (IJ k) (fun e =>
    letB (Nat.land e (nat_lit 65535)) (fun i => letB (Nat.shiftRight e (nat_lit 16)) (fun j =>
      andB (Nat.blt i k) (andB (Nat.blt j k) (Nat.beq (mul (RS i) (RS j)) (RS k))))))))

@[expose] noncomputable def slpOK (mul : Nat → Nat → Nat) (vld : Nat → Bool) (RS IJ : Nat → Nat)
    (n lo : Nat) : Bool :=
  allBelow (nat_lit 16) (nat_lit 1) (fun t => letB (Nat.add lo t) (fun k =>
    bIf(Nat.blt k n, slpStep mul vld RS IJ k, true)))

end CFSG.KC.Fi24Orb

end
