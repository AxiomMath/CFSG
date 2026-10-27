module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8GoodAll
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KAssemble
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24Main
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Thirty
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_25_holds_of_inputs
    (D : Data G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (hx : DataExt D) (hσ3 : SigmaThree D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h119 : F11.R119 D)
    (hSpA : RSp6SmallMod) (hSpC : RSp6SpinCent) (hSpF : RSp6SpinForm) (hSpSt : RSp6SpinStab)
    (hSchur : C8SchurSp6) (h95 : F09.R95Two D) (hu37 : U37Outer)
    (hSz : Inputs1719.K_CatalogueThreePrimeSz) : R16_25 D := by
  have h22 : R1622 D := R1622_of_R1621 D hSg h1219 h21
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have h129 : R129_1 D := r129_1_of_r127 D h127
  have l26 : R16_26 D := R16_26_of_fin D h61 (r16_26_fin_holds D h1217 hSpA hSpC hSpF hSpSt)
  have l24 : R16_24c D := r16_24c_holds D h126 hSg h1219 h21 hx h61 h127 h1214 l26
  have hg : C8Glob D := ⟨hx, hσ3, hSg, h1219, h61, h1217, hSpA, hSpC, h95, hu37, hSz⟩
  have l27_4 : R16_27_4 D :=
    r16_27_4_of_good D h61 h129 h22 h1217 hSpA hSpC hSpF hSpSt h127 h119 hSchur
      (c8TleKGood_holds D hg) (c8InvThreePrimeGood_holds D hg)
  have h28 : R16_28 D :=
    sixteen_twentyEight_of D (sixteen_twentyEight_r D l26) (R16_28_m_of_R16_26 D l26)
  have l30 : R16_30 D := r16_30_of D h22 l27_4 h28
  exact sixteen_twentyFive_of_inputs D hSg h1219 h21 h22 h129 h61 l24 l27_4 h28 l30

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
