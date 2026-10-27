module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.TripleCoverLift.Check

public section

namespace CFSG.KC.OpsV4

open CFSG.SectionRank.Native CFSG.KC.OpsK CFSG.KC.OpsMN CFSG.KC.LQT CFSG.KC.OpsLayK

variable {V : Type}

@[expose] noncomputable def conjG (O : Ops Nat V) (X T T₁ T₂ T₁₂ : Nat) : Bool :=
  forceB (O.mul X T) fun XT =>
    O.eq XT (O.mul T₁ X) || O.eq XT (O.mul T₂ X) || O.eq XT (O.mul T₁₂ X)

@[expose] noncomputable def relG (O : Ops Nat V) (D : LiftData) (g : Nat → Nat) :
    LiftRel → Bool
  | .inv n i => decide (n < D.base.nregs) && decide (i < D.base.outs.length) &&
      D.units.any (fun u => u.1 == n) &&
      O.eq (O.mul (g n) (g (D.base.outs.getD i 0)))
        (O.mul (O.mul (g (D.base.outs.getD i 0)) (g (D.base.outs.getD i 0))) (g n))
  | .fix n i => decide (n < D.base.nregs) && decide (i < D.base.outs.length) &&
      D.units.any (fun u => u.1 == n) &&
      O.eq (O.mul (g n) (g (D.base.outs.getD i 0))) (O.mul (g (D.base.outs.getD i 0)) (g n))
  | .swap n i j => decide (n < D.base.nregs) && decide (i < D.base.outs.length) &&
      decide (j < D.base.outs.length) && D.units.any (fun u => u.1 == n) &&
      O.eq (O.mul (g n) (g (D.base.outs.getD i 0))) (O.mul (g (D.base.outs.getD j 0)) (g n)) &&
      O.eq (O.mul (g n) (g (D.base.outs.getD j 0))) (O.mul (g (D.base.outs.getD i 0)) (g n))

@[expose] noncomputable def liftG (O : Ops Nat V) (pw : Nat → Nat → Nat) (D : LiftData)
    (g : Nat → Nat) : Bool :=
  D.base.outs.all (decide <| · < D.base.nregs) && decide (D.inv₁ < D.base.nregs) &&
    decide (D.inv₂ < D.base.nregs) &&
    O.elemOK (D.base.outs.map g) D.base.tests &&
    O.eq (O.mul (g D.inv₁) (g D.inv₁)) O.one && O.eq (O.mul (g D.inv₂) (g D.inv₂)) O.one &&
    O.commOK (g D.inv₁) (g D.inv₂) &&
    D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) (g D.inv₁)) (O.unit k)) &&
    forceB (O.mul (g D.inv₁) (g D.inv₂)) (fun T₁₂ => D.base.outs.all fun r =>
      conjG O (g r) (g D.inv₁) (g D.inv₁) (g D.inv₂) T₁₂ &&
        conjG O (g r) (g D.inv₂) (g D.inv₁) (g D.inv₂) T₁₂) &&
    D.units.all (fun u => decide (u.1 < D.base.nregs) && decide (0 < u.2) &&
      O.eq (pw (g u.1) u.2) O.one) &&
    D.rels.all (relG O D g)

@[expose] def v4Lift (D : Data) (inv₁ inv₂ : Nat) : LiftData := ⟨D, inv₁, inv₂, [], []⟩

@[expose] def regsL (D : LiftData) : List Nat :=
  D.base.outs ++ D.inv₁ :: D.inv₂ :: D.units.map Prod.fst

@[expose] noncomputable def liftN (O : Ops Nat V) (A B : Nat) (D : LiftData) : Bool :=
  decide (2 ≤ D.base.nregs) && D.base.prog.all (Op.lt D.base.nregs) &&
    regsN O A B D.base.nregs D.base.prog fun R =>
      liftG O (fun X e => powN O (e + 1) X e) D (getN R)

@[expose] noncomputable def v4N (O : Ops Nat V) (A B : Nat) (D : Data) (inv₁ inv₂ : Nat) : Bool :=
  liftN O A B (v4Lift D inv₁ inv₂)

@[expose] noncomputable def opsL (c : Lay) : Ops Nat Nat where
  decode _ := 0
  mul := c.mul
  one := c.ONE
  eq := Nat.beq
  vmul v X := c.vec v X
  unit := c.unit
  vne u w := !Nat.beq u w

@[expose] def liftPreL (c : Lay) (D : LiftData) : Bool :=
  progOK D.base.nregs D.base.prog && D.base.tests.all (decide <| · < c.d) &&
    D.units.all (fun u => decide (u.2 < 65536))

@[expose] noncomputable def liftL (c : Lay) (A B : Nat) (D : LiftData) : Bool :=
  liftPreL c D &&
    runC c D.base.prog (initR c A B D.base.nregs) fun R => liftG (opsL c) (powK c) D (getR c R)

@[expose] noncomputable def v4L (c : Lay) (A B : Nat) (D : Data) (inv₁ inv₂ : Nat) : Bool :=
  liftL c A B (v4Lift D inv₁ inv₂)

@[expose] noncomputable def liftFinL (c : Lay) (S : List Nat) (D : LiftData) : Bool :=
  liftG (opsL c) (powK c) D fun r => getR c S ((regsL D).idxOf r)

@[expose] noncomputable def v4FinL (c : Lay) (S : List Nat) (D : Data) (inv₁ inv₂ : Nat) : Bool :=
  liftFinL c S (v4Lift D inv₁ inv₂)

end CFSG.KC.OpsV4

end
