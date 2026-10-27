module

public import Certificates.Data.Kernel.LocalComp.Tits
public import Certificates.Data.CFSGNative.Filter.TitsElem

public noncomputable section

namespace CFSG.KC.LocalComp.Tits

open CFSG.KC.Enum CFSG.KS CFSG.SectionRank.Native.Tits

variable (n w : Nat)

@[expose] noncomputable def elemProdK (X0 X1 X2 X3 X4 k : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w)
    (ppow n w (mask w) (pidn n w) X0 (k % 2)) (ppow n w (mask w) (pidn n w) X1 (k / 2 % 2)))
    (ppow n w (mask w) (pidn n w) X2 (k / 4 % 2))) (ppow n w (mask w) (pidn n w) X3 (k / 8 % 2)))
    (ppow n w (mask w) (pidn n w) X4 (k / 16 % 2))

@[expose] noncomputable def commK (CP : List Nat) (X Y : Nat) : Bool :=
  eqOnK w CP (pcomp n w (mask w) X Y) (pcomp n w (mask w) Y X)

@[expose] noncomputable def invoK (CP : List Nat) (X : Nat) : Bool :=
  eqOnK w CP (ppow n w (mask w) (pidn n w) X 2) (pidn n w)

@[expose] noncomputable def elemK (TG : Nat → Nat) (CP : List Nat) (w0 w1 w2 w3 w4 : List Nat) :
    Bool :=
  strictB (wordK n w TG (texpand w0)) fun X0 => strictB (wordK n w TG (texpand w1)) fun X1 =>
  strictB (wordK n w TG (texpand w2)) fun X2 => strictB (wordK n w TG (texpand w3)) fun X3 =>
  strictB (wordK n w TG (texpand w4)) fun X4 =>
  lettersK ⟨w0 ++ w1 ++ w2 ++ w3 ++ w4, [], [], []⟩ &&
    allN 4 (fun s => permOK n w (mask w) (Nat.mul n w) (TG s) (pinvS n w (mask w) (TG s))) &&
    invoK n w CP X0 && invoK n w CP X1 && invoK n w CP X2 && invoK n w CP X3 &&
    invoK n w CP X4 &&
    commK n w CP X0 X1 && commK n w CP X0 X2 && commK n w CP X0 X3 && commK n w CP X0 X4 &&
    commK n w CP X1 X2 && commK n w CP X1 X3 && commK n w CP X1 X4 && commK n w CP X2 X3 &&
    commK n w CP X2 X4 && commK n w CP X3 X4 &&
    allN 31 (fun k => !eqOnK w CP (elemProdK n w X0 X1 X2 X3 X4 (k + 1)) (pidn n w))

end CFSG.KC.LocalComp.Tits

end
