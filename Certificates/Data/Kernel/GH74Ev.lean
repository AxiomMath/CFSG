module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.GH74

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def pcommK (n w p q : Nat) : Bool :=
  allN n fun i => Nat.beq (pg w (mask w) p (pg w (mask w) q i)) (pg w (mask w) q (pg w (mask w) p i))

@[expose] noncomputable def pcomm2K (n w a b q : Nat) : Bool :=
  allN n fun i => Nat.beq (pg w (mask w) a (pg w (mask w) b (pg w (mask w) q i)))
    (pg w (mask w) q (pg w (mask w) a (pg w (mask w) b i)))

@[expose] noncomputable def ppt (w p e i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) i (fun _ ih => pg w (mask w) p ih) e

@[expose] noncomputable def pfixK (n w e p : Nat) : Bool := allN n fun i => Nat.beq (ppt w p e i) i

@[expose] noncomputable def ord5K (n w z : Nat) : Bool :=
  bAnd(pfixK n w 5 z, bIf(pfixK n w 1 z, false, true))

@[expose] noncomputable def cent5Body (n w cnt : Nat) (T : Nat → Nat) (v z p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 :
    Nat) : Bool :=
  bAnd(allN cnt (fun i => bIf(pcommK n w (T i) z,
      bIf(Nat.beq (T i) p0, true, bIf(Nat.beq (T i) q0, true,
      bIf(Nat.beq (T i) p1, true, bIf(Nat.beq (T i) q1, true,
      bIf(Nat.beq (T i) p2, true, bIf(Nat.beq (T i) q2, true,
      bIf(Nat.beq (T i) p3, true, bIf(Nat.beq (T i) q3, true,
      bIf(Nat.beq (T i) p4, true, Nat.beq (T i) q4))))))))), true)),
    allN cnt (fun i => bIf(pcomm2K n w v (T i) z, false, true)))

@[expose] noncomputable def cent5At (n w cnt : Nat) (T : Nat → Nat) (t v z : Nat) : Bool :=
  bIf(ord5K n w z,
    strictB (pcomp n w (mask w) z (pidn n w)) (fun p1 => strictB (pcomp n w (mask w) z p1) (fun p2 =>
    strictB (pcomp n w (mask w) z p2) (fun p3 => strictB (pcomp n w (mask w) z p3) (fun p4 =>
    strictB (pcomp n w (mask w) t (pidn n w)) (fun q0 => strictB (pcomp n w (mask w) t p1) (fun q1 =>
    strictB (pcomp n w (mask w) t p2) (fun q2 => strictB (pcomp n w (mask w) t p3) (fun q3 =>
    strictB (pcomp n w (mask w) t p4) (fun q4 =>
      cent5Body n w cnt T v z (pidn n w) p1 p2 p3 p4 q0 q1 q2 q3 q4))))))))),
    true)

end CFSG.KS.GH74

end
