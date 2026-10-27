module

public import CFSG.RankThree.PartTwo.Sec21.HeringHullChain2
public import CFSG.RankThree.PartTwo.Sec21.HeringHullChain3

public section

namespace CFSG.RankThree.PartTwo.Sec21.HeringHull

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_lStar_le (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hG : TheoremFourHyp G)
    {A : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) (𝓟 : Set (Subgroup G))
    (h𝓟 : ∀ P ∈ 𝓟, IsQuasisimple P ∧ A ≤ Subgroup.normalizer (P : Set G))
    {Z₀ : Subgroup G} (hZ₀ : Z₀ ∈ thetaComponentFamily 3 A) (hZ₀P : ∀ P ∈ 𝓟, P ≤ Z₀) :
    ∃ Z ∈ lStar A, ∀ P ∈ 𝓟, P ≤ Z := by
  set S : Set (Subgroup G) := {Z | Z ∈ thetaComponentFamily 3 A ∧ ∀ P ∈ 𝓟, P ≤ Z} with hS
  set μ : Subgroup G → ℕ := fun Z => Nat.card (Z ⧸ aschbacherSolvableCore 3 Z) with hμ
  obtain ⟨Z, ⟨hZA, hZP⟩, hmax⟩ := Set.exists_max_image S μ S.toFinite ⟨Z₀, hZ₀, hZ₀P⟩
  refine ⟨Z, ⟨hZA, fun K hKA hZK => ?_⟩, hZP⟩
  obtain ⟨a, haA, ha1, hZa⟩ := mem_thetaComponentFamily_iff.mp hZA
  obtain ⟨a', ha'A, ha'1, hKa'⟩ := mem_thetaComponentFamily_iff.mp hKA
  by_cases hac : a ∈ thetaQuotCentralizer K
  · exact llRel_of_mem_thetaQuotCentralizer h45 h48 hG hAe hAn haA ha1 ha'A ha'1 hZa hKa' hZK hac
  · exfalso
    have hlt := card_quot_lt_of_llRel h45 h48 hG hAe hAn haA ha1 ha'A ha'1 hZa hKa' hZK hac
    have hKS : K ∈ S := ⟨hKA, fun P hP =>
      le_of_llRel_of_isQuasisimple h45 h48 hG hAe hAn haA ha1 ha'A ha'1 hZa hKa' hZK
        (h𝓟 P hP).1 (hZP P hP) (h𝓟 P hP).2⟩
    exact absurd (hmax K hKS) (not_le.mpr hlt)

end CFSG.RankThree.PartTwo.Sec21.HeringHull
