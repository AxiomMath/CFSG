module

public import Certificates.Data.Kernel.Misc.CentSrch

public section

namespace CFSG.KC.CentHead

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CentSrch

@[expose] noncomputable def headPt (n w : Nat) (LR TRI : Nat → Nat) (X X2 a : Nat) : Bool :=
  strictB (rpos w (mask w) (Nat.mul n w) (LR (nat_lit 0)) a) fun k0 =>
    bAnd(Nat.blt k0 (rcnt (LR (nat_lit 0))),
      strictB (Nat.add (roff n (Nat.mul n w) (LR (nat_lit 0))) k0) fun W1 =>
        strictB (rpos w (mask w) (Nat.mul n w) (LR (nat_lit 1))
          (invW w (mask w) TRI W1 (nat_lit 1) (pg w (mask w) X a))) fun k1 =>
          bAnd(Nat.blt k1 (rcnt (LR (nat_lit 1))),
            strictB (Nat.lor W1 (Nat.shiftLeft (Nat.add (roff n (Nat.mul n w) (LR (nat_lit 1))) k1)
              (nat_lit 16))) fun W2 =>
              Nat.blt (rpos w (mask w) (Nat.mul n w) (LR (nat_lit 2))
                (invW w (mask w) TRI W2 (nat_lit 2) (pg w (mask w) X2 a)))
                (rcnt (LR (nat_lit 2)))))

@[expose] noncomputable def headK (n w : Nat) (LR TRI : Nat → Nat) (X X2 LM : Nat) : Bool :=
  allN n fun a => !(headPt n w LR TRI X X2 a) ||
    Nat.beq (Nat.land (Nat.shiftRight LM a) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def idWord (n w : Nat) (LR : Nat → Nat) (BP : Nat) (i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l ih => Nat.lor ih (Nat.shiftLeft (Nat.add (roff n (Nat.mul n w) (LR l))
      (rpos w (mask w) (Nat.mul n w) (LR l) (pg w (mask w) BP l))) (Nat.mul (nat_lit 16) l))) i

@[expose] noncomputable def idImgs (w : Nat) (BP : Nat) (i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l ih => Nat.lor ih (Nat.shiftLeft (pg w (mask w) BP l) (Nat.mul w l))) i

@[expose] noncomputable def idPrefixOK (n w : Nat) (LR TR : Nat → Nat) (BP : Nat) (i : Nat) : Bool :=
  allN i fun l => strictB (rpos w (mask w) (Nat.mul n w) (LR l) (pg w (mask w) BP l)) fun k =>
    bAnd(Nat.blt k (rcnt (LR l)), Nat.beq (TR (Nat.add (roff n (Nat.mul n w) (LR l)) k)) (pidn n w))

end CFSG.KC.CentHead

end
