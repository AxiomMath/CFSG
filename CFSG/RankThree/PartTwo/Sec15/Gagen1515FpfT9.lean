module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCase1
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCase2
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCases

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

section Cert148


theorem exists_star
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142R)
    (h146 : Item146 A (lB A)) (h148 : Item148 A (lB A)) (h : Ctx A c L d) {g : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgX : g ∈ Subgroup.centralizer (x₀ L d : Set G)) (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1)
    (hgc : g * c * g⁻¹ = c * d) {T : Subgroup G} (hTX : T ≤ x₀ L d) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 ↥T) (hTQ : T ∈ scriptQ A (lB A))
    (h3 : ∀ T₀ : Subgroup G, T ≤ T₀ → IsPGroup 2 ↥T₀ →
      A ≤ Subgroup.normalizer (T₀ : Set G) →
      ∀ hY : Subgroup.normalizer (T₀ : Set G) ∈ scriptY A,
        letI := ker148_normal hY.2
        ¬ Case148Three A (lB A) (Subgroup.normalizer (T₀ : Set G))) :
    ∃ T₀ ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), g ∈ Subgroup.normalizer (T₀ : Set G) := by
  classical
  have hgT : g ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer (T : Set G)
      (Subgroup.centralizer_le (show (T : Set G) ⊆ (x₀ L d : Set G) from hTX) hgX)
  let 𝒯 : Set (Subgroup G) :=
    {T' | IsPGroup 2 ↥T' ∧ T' ∈ scriptQ A (lB A) ∧ T ≤ T' ∧
      g ∈ Subgroup.normalizer (T' : Set G)}
  have hT𝒯 : T ∈ 𝒯 := ⟨hT2, hTQ, le_rfl, hgT⟩
  obtain ⟨T₀, hT₀max⟩ := (Set.toFinite 𝒯).exists_maximalFor
    (fun T' : Subgroup G => Nat.card T') 𝒯 ⟨T, hT𝒯⟩
  obtain ⟨hT₀2, hT₀Q, hTT₀, hgT₀⟩ := hT₀max.1
  have hmax : ∀ T' : Subgroup G, IsPGroup 2 ↥T' → T' ∈ scriptQ A (lB A) → T ≤ T' →
      g ∈ Subgroup.normalizer (T' : Set G) → Nat.card T' ≤ Nat.card T₀ := by
    intro T' hT'2 hT'Q hTT' hgT'
    by_cases hle : Nat.card T' ≤ Nat.card T₀
    · exact hle
    · exact hT₀max.2 ⟨hT'2, hT'Q, hTT', hgT'⟩ (Nat.le_of_not_ge hle)
  have hAT₀ : A ≤ Subgroup.normalizer (T₀ : Set G) := (mem_scriptQ_iff.mp hT₀Q).2.1
  have hY : Subgroup.normalizer (T₀ : Set G) ∈ scriptY A := by
    refine ⟨?_, hAT₀.trans Subgroup.le_normalizer⟩
    intro htop
    have hnormal : T₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hT₀ne : T₀ ≠ ⊥ := by
      intro hbot
      apply hT
      rw [hbot] at hTT₀
      exact le_bot_iff.mp hTT₀
    haveI : IsSimpleGroup G := h.sec13Data.isSimpleGroup
    haveI : T₀.Normal := hnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T₀ with hbot | htop'
    · exact hT₀ne hbot
    · have h3dvdG : 3 ∣ Nat.card G := by
        have h3A : 3 ∣ Nat.card A := by rw [h.isE27.2]; norm_num
        exact h3A.trans (Subgroup.card_subgroup_dvd_card A)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT₀2
      have hG : Nat.card G = 2 ^ n := by
        rw [← Subgroup.card_top (G := G), ← htop']
        exact hn
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (hG ▸ h3dvdG)
      norm_num at h32
  letI := ker148_normal hY.2
  have hcases : Item148Cases A (lB A) (Subgroup.normalizer (T₀ : Set G)) := by
    have hAt := (item148_iff A (lB A)).mp h148 (Subgroup.normalizer (T₀ : Set G)) hY
    exact hAt.2
  rcases hcases with h1 | h2 | h3c | h4 | h5 | h6 | h7
  · exact ⟨T₀, mem_star_of_case1 h146 h hgA hg3 hT₀2 hT₀Q hTT₀ hgT₀ hmax h1, hgT₀⟩
  · exact absurd h2 (not_case2 h134 h48 h142 h hgA hgX hgc hTX hT hTT₀ hT₀2 hgT₀ hY)
  · exact absurd h3c (h3 T₀ hTT₀ hT₀2 hAT₀ hY)
  · exact absurd h4 (not_case467 h134 h48 h hY).1
  · exact absurd h5 (not_case5 h134 h48 h hY)
  · exact absurd h6 (not_case467 h134 h48 h hY).2.1
  · exact absurd h7 (not_case467 h134 h48 h hY).2.2

end Cert148

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
