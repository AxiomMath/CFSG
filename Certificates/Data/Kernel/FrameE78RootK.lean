module

public import Certificates.Data.Kernel.FrameE78K

public section

namespace CFSG.KC.FrameE78

open CFSG.KC.Enum

@[expose] noncomputable def addV3 (n u v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p ih => Nat.lor ih (Nat.shiftLeft
      (Nat.mod (Nat.add (ln u p) (ln v p)) (nat_lit 3)) (Nat.mul (nat_lit 2) p))) n

@[expose] noncomputable def rtMask (m RP : Nat) : Nat :=
  foldN m (fun a s => Nat.lor s (Nat.lor (Nat.shiftLeft (nat_lit 1) (rC RP a))
    (Nat.shiftLeft (nat_lit 1) (negL (rC RP a))))) (nat_lit 1)

@[expose] noncomputable def rtCnt (n m RP Tm y : Nat) : Nat :=
  cntN m fun a => bAnd(bitB Tm a, Nat.beq (dot3 n (rc RP a) y) (nat_lit 0))

@[expose] noncomputable def rtPlane (n m RP M x xn Tm y : Nat) : Bool :=
  bIf(Nat.blt (rtCnt n m RP Tm y) (nat_lit 13), true,
    orB (bitB M y) (orB (bitB M (addV3 n y x)) (bitB M (addV3 n y xn))))

@[expose] noncomputable def rtRep (n m RP V b Tm lo len : Nat) : Bool :=
  strictB (cntN m (bitB Tm)) fun t =>
    bIf(orB (Nat.beq t (nat_lit 21)) (Nat.beq t (nat_lit 36)),
      strictB (vget V b) fun x => strictB (negL x) fun xn => strictB (rtMask m RP) fun M =>
        allN len fun j => rtPlane n m RP M x xn Tm (vget V (Nat.add lo j)),
      true)

end CFSG.KC.FrameE78

end
