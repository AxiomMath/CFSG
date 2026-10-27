module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.PCos

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def cosPtK (n w m jc : Nat) (JT : Nat → Nat) (kw : Nat) (W : Nat → Nat)
    (kg : Nat) (G : Nat → Nat) (X e s : Nat) : Bool :=
  strictB (fld(e, nat_lit 0, nat_lit 255)) (fun k => strictB (fld(e, nat_lit 8, nat_lit 255))
    (fun j => bAnd(Nat.blt j jc, bIf(Nat.blt k kw, Nat.beq s (pcomp n w m (W k) (JT j)),
      strictB (Nat.sub k kw) (fun c => bAnd(Nat.blt c kg,
        Nat.beq (pcomp n w m (pcomp n w m (pcomp n w m X s) (JT j)) (G c))
          (pcomp n w m (G c) s)))))))

@[expose] noncomputable def cosK (n w m cnt : Nat) (T : Nat → Nat) (jc : Nat) (JT : Nat → Nat)
    (kw : Nat) (W : Nat → Nat) (kg : Nat) (G : Nat → Nat) (X : Nat) (E : Nat → Nat) : Bool :=
  allN cnt (fun q => strictB (E q) (fun e => cosPtK n w m jc JT kw W kg G X e (T q)))

end CFSG.KS.PCos

end
