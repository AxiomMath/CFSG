module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSimpleComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1SchurU4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3Omega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s15_eq_one_of_omega_minus_six_component
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1) :
    s15 D.M V₀ V hV L = 1 := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c1_isSimpleGroup_of_isOmegaMinus_six hOm
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) := by
    obtain ⟨E, hE, hEcard⟩ := s15k_om6_exists_e27 hOm
    exact CFSG.SectionRank.le_pRank (p := 3) (k := 3) (by norm_num) (H := ⊤) (E := E)
      le_top hE (by rw [hEcard]; norm_num)
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      IsPGroup 2 ↥(Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    have hU4 : IsU4 (Q ⧸ Subgroup.center Q) 1 :=
      CFSG.Blueprint.LieModel.of_mulEquiv eQ.symm (isU4_of_isOmegaMinus_six hOm)
    have hdvd := rSchurOm6_holds Q hQ hU4
    exact IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hdvd)
  exact s15_eq_one_of_simple_component_of_three_rank c hcomp hsimple (r := 3) (by norm_num)
    hrank hcover

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
