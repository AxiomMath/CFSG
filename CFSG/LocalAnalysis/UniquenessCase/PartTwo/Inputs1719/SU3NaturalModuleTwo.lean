module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleTwoDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem altTwo_u34_of_mParam_autSub_lt
    (hW : ∀ w : W, w ^ 2 = 1) {Y K : Subgroup (MulAut W)}
    (hKY : K ≤ Y) (hKcomp : CFSG.Open.IsComponentOf K Y) (hSU : IsSU3 ↥K 2)
    (hsum : IsDirSumOver (conjSet K Y) (fun X => commV (autQuot X (⊥ : Subgroup W))))
    {I : Subgroup W} (hI : I ∈ irrSet K)
    (hmI : E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
      (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) < 2 * 2 + 2) :
    NatSUn (autQuot (autSub (autQuot K (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W))))
        (fixV (autSub (autQuot K (⊥ : Subgroup W))
          (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))))) ⊤ ⊥ 3 2 ∧
      2 * 2 ≤ E3.mParam (autSub (autQuot Y (⊥ : Subgroup W))
        (I.map (QuotientGroup.mk' (⊥ : Subgroup W)))) :=
  altTwo_su3_of_mParam_autSub_lt hW hKY hKcomp le_rfl hSU hsum hI (by omega)

theorem k_SU3NaturalModuleTwo_of_w4
    (h128 : W4Lem12_8) : K_SU3NaturalModuleTwo := by
  intro W _ _ hWsq Y K hKY hKcomp _ hSU hO2 hbasic hfix hmY
  obtain ⟨hCN, hm, -⟩ :=
    su3NaturalModule_of_w4 h128 hWsq hKY hKcomp hSU le_rfl hO2 hbasic hfix (by omega)
  exact ⟨hCN, hm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
