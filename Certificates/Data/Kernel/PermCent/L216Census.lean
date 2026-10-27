module

public import Certificates.Data.Kernel.PermCent.L216Twin

public section

namespace CFSG.Certificates.Kernel.PkCV.L216C

open CFSG.GH74.Uniqueness.SU.K.R4.L216M CFSG.Certificates.Kernel.PkCV.KGrp

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def strictLN (l : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun a _ ih k => Nat.rec (motive := fun _ => Bool) (ih fun t => k (nat_lit 0 :: t))
      (fun m _ => ih fun t => k (Nat.succ m :: t)) a) l k

@[expose] noncomputable def memN (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ r => Bool.rec (motive := fun _ => Bool) r true (Nat.beq a x)) L

@[expose] noncomputable def clsV (r : CV 17) : List Nat :=
  (elemsC QP).map fun g => (g * r * g⁻¹).1

@[expose] noncomputable def r1 : CV 17 := cOf pa

@[expose] noncomputable def r2 : CV 17 := cOf sg * cOf sg

@[expose] noncomputable def clsOK (L : List (CV 17)) (C1 C2 : List Nat) : Bool :=
  L.all fun t => !powOneC t 2 || decide (t = 1) ||
    strictB t.1 fun x => memN x C1 || memN x C2

@[expose] noncomputable def clsBlk (c j : Nat) : Bool :=
  strictLN (clsV r1) fun C1 => strictLN (clsV r2) fun C2 =>
    clsOK (((elemsC QA).drop (j * c)).take c) C1 C2

end CFSG.Certificates.Kernel.PkCV.L216C

end
