module

public import Certificates.Data.Kernel.L34Inv
public import Certificates.Data.Kernel.Spor.HNAOrb

public section

namespace CFSG.KC.GrpWit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KLie.CT (fget andB orB notB)

@[expose] noncomputable def commK (n w lo len NC : Nat) (C : Nat → Nat) (ND : Nat) (D : Nat → Nat)
    (fw : Nat) (CW : Nat → Nat) : Bool :=
  allN len fun i => strictB (Nat.add lo i) fun a => strictB (C a) fun x => strictB (CW a) fun row =>
    allN NC fun b => strictB (fget row b fw) fun q =>
      andB (Nat.blt q ND) (Nat.beq (D q) (CFSG.KS.HNA.commP n w x (C b)))

@[expose] noncomputable def invWitK (n w e a ND : Nat) (D : Nat → Nat) (NQ : Nat) (Q DW : Nat → Nat) :
    Bool :=
  allN ND fun d => strictB (D d) fun x =>
    orB (notB (Nat.beq (pcomp n w (mask w) x x) e))
      (strictB (DW d) fun j => andB (Nat.blt j NQ) (Nat.beq (Q j) (pcomp n w (mask w) a x)))

@[expose] noncomputable def centMemK (n w a ng : Nat) (G : Nat → Nat) (NM : Nat) (M CM : Nat → Nat) :
    Bool :=
  allN ng fun k => strictB (G k) fun g =>
    andB (Nat.beq (pcomp n w (mask w) a g) (pcomp n w (mask w) g a))
      (strictB (CM k) fun j => andB (Nat.blt j NM) (Nat.beq (M j) g))

@[expose] noncomputable def permsK (n w N : Nat) (T : Nat → Nat) : Bool :=
  allN N fun i => strictB (T i) fun t => permOK n w (mask w) (Nat.mul n w) t (pinvS n w (mask w) t)

end CFSG.KC.GrpWit

end
