module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListMain
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native312
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312SL2Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverFinal
public import CFSG.Quasithin.Background.A3FactsAssembly

public section

namespace CFSG.Quasithin.A38c14

open CFSG.QuasithinUnique.Vol2Native
open CFSG.QuasithinUnique.Vol2Native.A312L

structure A312ResidualRest : Prop where
  l3odd : FamL3odd
  u3odd : FamU3odd
  m23 : FamM23
  m24 : FamM24
  j1 : FamJ1
  j2 : FamJ2
  j4 : FamJ4
  hs : FamHs
  he : FamHe
  ru : FamRu
  sl3odd : FamSl3odd
  hat7 : FamHat7
  hatM22 : FamHatM22

theorem A312ResidualRest.toResidual (h : A312ResidualRest) :
    A312Residual :=
  ⟨h.l3odd, h.u3odd, m22, h.m23, h.m24, h.j1, h.j2, h.j4, h.hs, h.he, h.ru, h.sl3odd, h.hat7,
    h.hatM22⟩

theorem a312ForSQTK_of_residual

    (ha134 : A3Facts.A134ForSQTK) (hS : A3Facts.SchreierSQTK) (hR : A312ResidualRest) :
    A312ForSQTK := by
  have h36 := a36CoreForSQTKCat_of_a129 CFSG.Quasithin.a129One
  have h37 := a37ForSQTKCat_of_core h36
  have h38 := A3Facts.a38ForSQTKCat_of_a134ForSQTK ha134 h36 h37
  have h39 := A3Facts.a39ForSQTKCat_of_schreierSQTK hS h36 h37 h38
  exact a312ForSQTK_of_cat
    (a312ForSQTKCat_of_facts (a312ListFactsCat_of_residual threeCoverFactCat hR.toResidual)
      a312SL2Fact h36 h37 h39)

end CFSG.Quasithin.A38c14
