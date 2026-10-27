module

public import CFSG.Sporadic.Schreier.Co3GenerationCheck
public meta import CFSG.Sporadic.Schreier.Co3GenerationCheck
public import CFSG.Sporadic.Schreier.Co3SecondImageCheckInputs
public import Certificates.Certificate2160

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

theorem co3D0Img_check :
    co3D0ImgRec.1.size = 192 ∧ eqA 12 co3D0ImgRec.1[0]! (idA 12) = true ∧
    (∀ i < 192, 1 ≤ i → co3D0ImgRec.2.1[i]! < i ∧ co3D0ImgRec.2.2[i]! < 5 ∧
      eqA 12 co3D0ImgRec.1[i]!
        (compA 12 co3D0Kappa1[co3D0ImgRec.2.2[i]!]! co3D0ImgRec.1[co3D0ImgRec.2.1[i]!]!) = true) ∧
    (∀ i < 192, isInvA 12 co3D0ImgRec.1[i]! (invCand 12 co3D0ImgRec.1[i]!) = true) ∧
    (∀ k < 5, isInvA 12 co3D0Kappa1[k]! (invCand 12 co3D0Kappa1[k]!) = true) ∧
    (∀ k < 5, ∀ i < 192, ∃ j < 192,
      eqA 12 (compA 12 co3D0Kappa1[k]! co3D0ImgRec.1[i]!) co3D0ImgRec.1[j]! = true) ∧
    (∀ k < 5, ∀ i < 192, ∃ j < 192,
      eqA 12 (compA 12 (invCand 12 co3D0Kappa1[k]!) co3D0ImgRec.1[i]!) co3D0ImgRec.1[j]! = true) ∧
    (∀ i < 192, ∀ j < i, eqA 12 co3D0ImgRec.1[i]! co3D0ImgRec.1[j]! = false) :=
  Certificates.certificate2160

end CFSG.Sporadic.Schreier.Co3
