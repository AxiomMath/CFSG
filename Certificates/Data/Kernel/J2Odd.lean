module

public import Certificates.Data.Kernel.J2Enum

public section

namespace CFSG.KC.J2Odd

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Enum

@[expose] noncomputable def oddOne (n w m : Nat) (L : List Nat) (x e : Nat) : Bool :=
  strictB (Nat.land e 3) (fun t => strictB (Nat.land (Nat.shiftRight e 2) 511) (fun p =>
  strictB (lget L (Nat.land (Nat.shiftRight e 11) 2047)) (fun h1 =>
  strictB (lget L (Nat.land (Nat.shiftRight e 22) 2047)) (fun h2 =>
  strictB (pinvS n w (mask w) h1) (fun i1 => strictB (pinvS n w (mask w) h2) (fun i2 =>
  bIf(Nat.beq t 0, Nat.beq x (pidn n w), bAnd(Nat.blt p n,
  bIf(Nat.beq t 1, bIf(Nat.beq (itP (fun q => pg w (mask w) x q) m p) p, false, true),
  bAnd(permOK n w (mask w) (Nat.mul n w) h1 i1,
  bIf(Nat.beq t 2, bIf(Nat.beq (itP (fun q => pg w (mask w) x (pg w (mask w) h1
      (pg w (mask w) x (pg w (mask w) i1 q)))) m p) p, false, true),
    bAnd(permOK n w (mask w) (Nat.mul n w) h2 i2,
    bIf(Nat.beq (itP (fun q => pg w (mask w) x (pg w (mask w) h1 (pg w (mask w) x (pg w (mask w) i1
      (pg w (mask w) h2 (pg w (mask w) x (pg w (mask w) i2 q))))))) m p) p, false, true)))))))))))))

@[expose] noncomputable def oddK (n w m : Nat) (L W : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun x _ ih W => bAnd(oddOne n w m L x (lget W 0),
      ih (List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) W))) L W

end CFSG.KC.J2Odd

end
