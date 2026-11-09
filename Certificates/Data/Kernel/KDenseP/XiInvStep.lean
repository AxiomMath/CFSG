module

public import Certificates.Data.Kernel.KDenseP.Letters
public import Certificates.Data.Kernel.YModel.Model

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense CFSG.KC.KDenseP
open CFSG.Monster.AxisCount

@[expose] noncomputable def colxiTN (S n lg b0 b1 R x : Nat) : Nat :=
  negMN S n (Nat.land R (Nat.land (clrN S b0) (clrN S b1)))
    (bflyN S n lg b0 R (bflyN S n lg b1 R
      (dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) b1) (Nat.shiftLeft (nat_lit 1) b0))
        (repN S n (Nat.land R (Nat.land (idPlane S b0) (clrN S b1)))) x)))

@[expose] noncomputable def xiInvStepN (n lg : Nat) (F : Fix) (XN PN : Nat) (X A W : Nat) :
    Nat × Nat × Nat :=
  (negMN SX n F.xiSgn (netN SX n (nat_lit 17) XN X),
    rotN SA n (dvN n (nat_lit 2))
      (colxiTN SA n lg (nat_lit 5) (nat_lit 6) valA (colxiTN SA n lg (nat_lit 0) (nat_lit 1) valA A)),
    rotN SX n (dvN n (nat_lit 3)) (colxiTN SX n lg (nat_lit 0) (nat_lit 1) valW (negMN SX n dinM
      (pinWN n (wht4N n lg (netN SX n (nat_lit 17) PN (negMN SX n doutM W)))))))

end CFSG.KC.KStep

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.KDense CFSG.Monster.AxisCount

@[expose] noncomputable def xiInvSt (n lg : Nat) (F : Fix) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun ok r => Prod.rec (motive := fun _ => St) (fun X r2 =>
    Prod.rec (motive := fun _ => St) (fun A W =>
      Prod.rec (motive := fun _ => St) (fun X' r5 => (ok, X', r5))
        (CFSG.KC.KStep.xiInvStepN n lg F (CFSG.KC.YModel.netRev (nat_lit 17) F.xiNet)
          (CFSG.KC.YModel.netRev (nat_lit 17) F.pout) X A W)) r2) r) s

@[expose] noncomputable def isXiB (g : Native.Gen) : Bool :=
  Native.Gen.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => false) (fun _ => false) true false g

@[expose] noncomputable def headXiB (w : List Native.Gen) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun g _ _ => isXiB g) w

end CFSG.KC.KDenseP

end
