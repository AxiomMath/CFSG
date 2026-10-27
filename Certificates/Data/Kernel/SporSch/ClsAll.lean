module

public import Certificates.Data.Kernel.SporSch.J1Pt

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11

@[expose] noncomputable def eqAllK (n : Nat) (f g : Nat → Nat) : Bool :=
  allN n (fun x => Nat.beq (f x) (g x))

@[expose] noncomputable def clsGK (n w m nw BP nb N ng mx : Nat) (G GI LR TR : Nat → Nat)
    (E CL O IX PA LB DP : Nat → Nat) (K ncl k : Nat) : Bool :=
  bIf(Nat.blt k K, strictB (E k) (fun j => strictB (CL k) (fun i =>
    strictB (O i) (fun lo => strictB (O (Nat.succ i)) (fun hi =>
    bAnd(Nat.blt i ncl, bAnd(Nat.ble lo k, bAnd(Nat.blt k hi, bAnd(Nat.blt j N,
    bAnd(bIf(Nat.blt (Nat.succ k) hi, Nat.blt j (E (Nat.succ k)), true),
    bAnd(ordF w m BP nb (apL w m (elemT n nw LR TR nb j)) mx,
    bAnd(allN ng (fun l => strictB (IX (Nat.add (Nat.mul ng k) l)) (fun p =>
      bAnd(Nat.ble lo p, bAnd(Nat.blt p hi,
        eqB w m BP nb (conjF w m (G l) (GI l) (apL w m (elemT n nw LR TR nb j)))
          (apL w m (elemT n nw LR TR nb (E p))))))),
    bIf(Nat.beq k lo, Nat.beq (DP k) (nat_lit 0),
      strictB (PA k) (fun p => strictB (LB k) (fun l =>
        bAnd(Nat.ble lo p, bAnd(Nat.blt p hi, bAnd(Nat.blt (DP p) (DP k), bAnd(Nat.blt l ng,
          eqB w m BP nb (apL w m (elemT n nw LR TR nb j))
            (conjF w m (G l) (GI l) (apL w m (elemT n nw LR TR nb (E p)))))))))))))))))))))),
    true)

@[expose] noncomputable def clsGHdK (n w m nw nb : Nat) (LR TR : Nat → Nat) (E O : Nat → Nat)
    (K ncl zp Z : Nat) : Bool :=
  bAnd(Nat.beq (O (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (O ncl) K,
  bAnd(allN ncl (fun i => Nat.blt (O i) (O (Nat.succ i))),
  bAnd(allN ncl (fun i => bIf(Nat.blt (Nat.succ i) ncl,
    Nat.blt (E (O i)) (E (O (Nat.succ i))), true)),
  bAnd(Nat.blt zp K,
    eqAllK n (apL w m (elemT n nw LR TR nb (E zp))) (fun x => pg w m Z x))))))

end CFSG.KS.SporSch.MOC

end
