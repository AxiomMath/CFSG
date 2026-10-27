module

public import CFSG.RankThree.PartOne.S11d.LowRank
public import CFSG.RankThree.Chevalley.SteinbergBTEvenEModelFieldTwo
public import CFSG.RankThree.Chevalley.SteinbergBNHigherExceptionalSmallField
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.Chevalley

theorem chevalleyModel_of_lieModel_exc {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (h1 : t ∉ Blueprint.classicalTags) (h2 : t ∉ Blueprint.reeTitsTags) (h3 : t ≠ .twistedB2)
    (h : Blueprint.LieModel X t n 2 f) : Blueprint.ChevalleyExceptionalModel X t 2 f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by revert h1 h2 h3; cases t <;> decide)

theorem chevalleyExceptionalModel_congr {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {t : StatedLieTag} {p f : ℕ} (h : Blueprint.ChevalleyExceptionalModel G t p f) :
    Blueprint.ChevalleyExceptionalModel H t p f := by
  obtain ⟨hadm, hm⟩ := h
  refine ⟨hadm, ?_⟩
  cases t <;> first
    | exact False.elim hm
    | (obtain ⟨K, hKf, hKfin, hK, ⟨φ⟩⟩ := hm
       exact ⟨K, hKf, hKfin, hK, ⟨e.symm.trans φ⟩⟩)
    | (obtain ⟨K, hKf, hKfin, hK, σ, hσ, ⟨φ⟩⟩ := hm
       exact ⟨K, hKf, hKfin, hK, σ, hσ, ⟨e.symm.trans φ⟩⟩)


theorem false_of_even_exceptional_model_J {J : Type} [Group J] [Finite J]
    (he : CFSG.twoLocalOddRank J ≤ 3) {τ : StatedLieTag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6) {f : ℕ} (hf : 2 ≤ f)
    (hmod : Blueprint.ChevalleyExceptionalModel (J ⧸ Subgroup.center J) τ 2 f) : False := by
  have hmod' : Blueprint.ChevalleyExceptionalModel
      (↥(⊤ : Subgroup J) ⧸ Subgroup.center ↥(⊤ : Subgroup J)) τ 2 f :=
    chevalleyExceptionalModel_congr (QuotientGroup.congr _ _ Subgroup.topEquiv.symm
      (Subgroup.map_center_eq Subgroup.topEquiv.symm)) hmod
  rcases hτ with rfl | hτ
  · have h := (actual_central_cover_higher_exceptional_small_field_restrictions he ⊤
      (Or.inl rfl) hmod').2.1 rfl rfl
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  · have hf1 := actual_central_cover_even_E_model_field_two he ⊤ (by omega) hτ hmod'
    omega

theorem TCX.highRankFalse_E6 : TCX.HighRankFalse .E6 := by
  intro _ J _ _ p n f₀ _ hp hp5 hf₀ _ _ he hM _
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  refine false_of_even_exceptional_model_J ?_ (Or.inr (Or.inl rfl)) (by omega)
    (chevalleyModel_of_lieModel_exc (by decide) (by decide) (by decide) hM)
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact he

theorem TCX.highRankFalse_E7 : TCX.HighRankFalse .E7 := by
  intro _ J _ _ p n f₀ _ hp hp5 hf₀ _ _ he hM _
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  refine false_of_even_exceptional_model_J ?_ (Or.inr (Or.inr (Or.inl rfl))) (by omega)
    (chevalleyModel_of_lieModel_exc (by decide) (by decide) (by decide) hM)
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact he

theorem TCX.highRankFalse_E8 : TCX.HighRankFalse .E8 := by
  intro _ J _ _ p n f₀ _ hp hp5 hf₀ _ _ he hM _
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  refine false_of_even_exceptional_model_J ?_ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by omega)
    (chevalleyModel_of_lieModel_exc (by decide) (by decide) (by decide) hM)
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact he

theorem TCX.highRankFalse_twistedE6 : TCX.HighRankFalse .twistedE6 := by
  intro _ J _ _ p n f₀ _ hp hp5 hf₀ _ _ he hM _
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  refine false_of_even_exceptional_model_J ?_ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by omega)
    (chevalleyModel_of_lieModel_exc (by decide) (by decide) (by decide) hM)
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact he

theorem TCX.highRankFalse_F4 : TCX.HighRankFalse .F4 := by
  intro _ J _ _ p n f₀ _ hp hp5 hf₀ _ _ he hM _
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  refine false_of_even_exceptional_model_J ?_ (Or.inl rfl) (by omega)
    (chevalleyModel_of_lieModel_exc (by decide) (by decide) (by decide) hM)
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact he

end CFSG.RankThree.PartOne
