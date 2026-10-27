module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def forestAtG (n kG R : Nat) (g : Nat → Nat → Nat)
    (Q ORD FO DEP PAR GL : Nat → Nat) (t : Nat) : Bool :=
  strictB (Q t) (fun q => bAnd(Nat.blt q n, bAnd(Nat.beq (ORD q) t,
    bIf(Nat.blt t R,
      bAnd(Nat.beq (DEP q) 0, bAnd(Nat.beq (PAR q) 0, Nat.beq (GL q) 0)),
      strictB (FO t) (fun f => strictB (Nat.div f kG) (fun h =>
        strictB (Nat.mod f kG) (fun k => strictB (Q h) (fun p =>
          bAnd(Nat.blt h t, bAnd(Nat.beq (g k p) q,
          bAnd(Nat.beq (PAR q) p, bAnd(Nat.beq (GL q) k,
          bAnd(Nat.beq (DEP q) (Nat.succ (DEP p)),
            bIf(Nat.blt (Nat.succ t) n, Nat.blt f (FO (Nat.succ t)), true))))))))))))))

@[expose] noncomputable def eventAtG (n kG R : Nat) (g : Nat → Nat → Nat) (Q ORD FO : Nat → Nat)
    (e : Nat) : Bool :=
  strictB (g (Nat.mod e kG) (Q (Nat.div e kG))) (fun y =>
    bAnd(Nat.blt y n, strictB (ORD y) (fun t => bIf(Nat.blt t R, true, Nat.ble (FO t) e))))

@[expose] noncomputable def partAtG (n kG R : Nat) (g : Nat → Nat → Nat)
    (LAB Q DEP PAR GL : Nat → Nat) (x : Nat) : Bool :=
  strictB (LAB x) (fun c =>
    bAnd(allN kG (fun k => strictB (g k x) (fun y => bAnd(Nat.blt y n, Nat.beq (LAB y) c))),
      bIf(Nat.beq (DEP x) 0,
        bAnd(Nat.blt c R, Nat.beq (Q c) x),
        strictB (PAR x) (fun p => strictB (GL x) (fun k =>
          bAnd(Nat.blt p n, bAnd(Nat.blt (DEP p) (DEP x),
            bAnd(Nat.blt k kG, Nat.beq (g k p) x))))))))

@[expose] noncomputable def rootAtG (n : Nat) (LAB Q : Nat → Nat) (k : Nat) : Bool :=
  strictB (Q k) (fun r => bAnd(Nat.blt r n, Nat.beq (LAB r) k))

end CFSG.KS.SporSch

end
