module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.KC.OpsCubN

open CFSG.SectionRank.Native CFSG.KC.OpsK CFSG.KC.OpsMN CFSG.KC.Loop

variable (O : Ops Nat Nat)

@[expose] noncomputable def pwN (X e : Nat) : Nat := powN O (Nat.succ e) X e

@[expose] noncomputable def appN (X : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun v => v) (fun _ ih v => strictN (O.vmul v X) ih)

@[expose] noncomputable def appBaseN (b : Nat) (xs : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
    (fun X _ ih n v => ih (n / b) (appN O X (n % b) v)) xs

@[expose] noncomputable def pairN : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) true (fun v vs ih => vs.all (fun w => O.vne v w) && ih)

@[expose] noncomputable def nfN (b : Nat) (xs : List Nat) (t : Nat) : Bool :=
  forceL ((List.range (b ^ xs.length)).map fun n => appBaseN O b xs n (O.unit t))
    fun L => pairN O L.reverse

@[expose] noncomputable def cubZ (D : CubData) (X Y H Z : Nat) : Bool :=
  O.eq (pwN O X D.r) O.one && O.eq (pwN O Y D.r) O.one && O.eq (pwN O H D.oh) O.one &&
    O.vne (O.vmul (O.unit D.t) Z) (O.unit D.t) &&
    O.eq (O.mul Z X) (O.mul X Z) && O.eq (O.mul Z Y) (O.mul Y Z) &&
    O.eq (O.mul H X) (O.mul (O.mul (O.mul (pwN O X D.a) (pwN O Y D.b)) (pwN O Z D.k)) H) &&
    O.eq (O.mul H Y) (O.mul (O.mul (O.mul (pwN O X D.c) (pwN O Y D.d)) (pwN O Z D.l)) H) &&
    O.eq (O.mul H Z) (O.mul (pwN O Z D.μ) H) && nfN O D.r [X, Y, Z] D.t

@[expose] noncomputable def cubN (D : CubData) (R : List Nat) : Bool :=
  forceB (O.mul (O.mul (O.mul (getN R D.rx) (getN R D.ry)) (pwN O (getN R D.rx) (D.r - 1)))
      (pwN O (getN R D.ry) (D.r - 1)))
    (cubZ O D (getN R D.rx) (getN R D.ry) (getN R D.rh))

@[expose] noncomputable def cubicN (A B : Nat) (D : CubData) : Bool :=
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.rx < D.nregs) &&
    decide (D.ry < D.nregs) && decide (D.rh < D.nregs) && decide (0 < D.r) &&
    decide (0 < D.oh) && regsN O A B D.nregs D.prog (cubN O D)

end CFSG.KC.OpsCubN

end
