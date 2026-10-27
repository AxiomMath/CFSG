module

public import Certificates.Data.Kernel.Co1PPin

public section

namespace CFSG.KC.Co1P

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT

@[expose] noncomputable def parK (R : Nat → Nat) (i : Nat) : Nat := Nat.div (R (Nat.sub i 1)) (nat_lit 8)

@[expose] noncomputable def labK (R : Nat → Nat) (i : Nat) : Nat := Nat.mod (R (Nat.sub i 1)) (nat_lit 8)

@[expose] noncomputable def pathK (act : Nat → Nat → Nat) (root : Nat) (R : Nat → Nat) :
    Nat → Nat → Nat × Bool :=
  Nat.rec (motive := fun _ => Nat → Nat × Bool) (fun i => Prod.mk root (Nat.beq i 0))
    (fun _ ih i => Bool.rec (motive := fun _ => Nat × Bool)
      (Prod.rec (motive := fun _ => Nat × Bool)
        (fun v ok => Prod.mk (act (labK R i) v) (CFSG.KLie.CT.andB ok (Nat.blt (parK R i) i))) (ih (parK R i)))
      (Prod.mk root true) (Nat.beq i 0))

@[expose] noncomputable def ptPK (GK GiK : List Nat) (R : Nat → Nat) (root d i : Nat) : Nat × Bool :=
  Prod.rec (motive := fun _ => Nat × Bool) (fun a oka => Prod.rec (motive := fun _ => Nat × Bool)
    (fun b okb => Prod.mk (mulWK (mulWK a root) b) (CFSG.KLie.CT.andB oka okb))
    (pathK (hisAct GiK) oneK R d i)) (pathK (hsAct GK) oneK R d i)

@[expose] noncomputable def keyAtP (N kw : Nat) (SK IX : Nat → Nat) (PF : Nat → Nat × Bool) (s : Nat) :
    Bool :=
  CFSG.KLie.CT.andB (keyAt N kw SK IX (fun i => (PF i).1) s) (PF (IX s)).2

@[expose] noncomputable def cntK (N : Nat) (f : Nat → Bool) (c : Nat) : Nat :=
  sumN (nat_lit 64) fun k => (fun i => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
    (CFSG.KLie.CT.andB (Nat.blt i N) (f i))) (Nat.add (Nat.mul (nat_lit 64) c) k)

end CFSG.KC.Co1P

end
