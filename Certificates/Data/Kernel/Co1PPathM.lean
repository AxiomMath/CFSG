module

public import Certificates.Data.Kernel.Co1PPath

public section

namespace CFSG.KC.Co1P

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT

@[expose] noncomputable def pathM (act : Nat → Nat → Nat) (T : Nat → Nat) (M : Nat) (R : Nat → Nat) :
    Nat → Nat → Nat × Bool :=
  Nat.rec (motive := fun _ => Nat → Nat × Bool) (fun i => Prod.mk (T i) (Nat.blt i M))
    (fun _ ih i => Bool.rec (motive := fun _ => Nat × Bool)
      (Prod.rec (motive := fun _ => Nat × Bool)
        (fun v ok => Prod.mk (act (labK R i) v) (CFSG.KLie.CT.andB ok (Nat.blt (parK R i) i))) (ih (parK R i)))
      (Prod.mk (T i) true) (Nat.blt i M))

@[expose] noncomputable def ptM (GK GiK : List Nat) (TH THi : Nat → Nat) (M : Nat) (R : Nat → Nat)
    (root d i : Nat) : Nat × Bool :=
  Prod.rec (motive := fun _ => Nat × Bool) (fun a oka => Prod.rec (motive := fun _ => Nat × Bool)
    (fun b okb => Prod.mk (mulWK (mulWK a root) b) (CFSG.KLie.CT.andB oka okb))
    (pathM (hisAct GiK) THi M R d i)) (pathM (hsAct GK) TH M R d i)

end CFSG.KC.Co1P

end
