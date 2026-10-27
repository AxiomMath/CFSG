module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreM6Defs
public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs

public section

namespace CFSG.StandardType.RCKBand

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

@[expose] def CaseEightV (t : StatedLieTag) (f p : ℕ) (A : Subgroup (ModGL (langTag t) GGL)) :
    Prop :=
  t = .twistedE6 ∧ p = 3 ∧ 3 ∣ 2 ^ f + 1 ∧ ¬ 9 ∣ 2 ^ f + 1 ∧ A ≤ ⁅ggFixGp t f, ggFixGp t f⁆

@[expose] def BandRankFloor (t : StatedLieTag) (f p : ℕ) (A : Subgroup (ModGL (langTag t) GGL)) :
    Prop :=
  p = 3 →
    ((t = .E7 ∨ t = .E8) → 3 ^ ((langTag t).rank - 1) ≤ Nat.card A) ∧
    (t = .E6 → Even f → 3 ^ 5 ≤ Nat.card A) ∧
    (t = .twistedE6 → 9 ∣ 2 ^ f + 1 → 3 ^ 5 ≤ Nat.card A) ∧
    (t = .twistedE6 → Odd f → ¬ A ≤ ⁅ggFixGp t f, ggFixGp t f⁆ → 3 ^ 5 ≤ Nat.card A)

private theorem three_dvd_two_pow_add_one {f : ℕ} (hf : Odd f) : 3 ∣ 2 ^ f + 1 := by
  obtain ⟨k, rfl⟩ := hf
  have h4 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
  rw [h2]
  omega

private theorem not_pow_four_le {p m : ℕ} (hp : 1 < p) (hm : m ≤ 3) {n : ℕ} (h4 : p ^ 4 ≤ n)
    (hn : n ≤ p ^ m) : False := by
  have h1 : p ^ m ≤ p ^ 3 := Nat.pow_le_pow_right (by omega) hm
  have h2 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp (by norm_num)
  omega

theorem ggLieToralBandRCK_of_M6c
    (h6c : GGLieNonToralRankFour) :
    ∀ (t : StatedLieTag), GGExcFive t → ∀ (f : ℕ), 1 ≤ f → ∀ (p : ℕ), p.Prime →
      ∀ A : Subgroup (ModGL (langTag t) GGL), A ≤ ggFixGp t f → IsElemAbelian p A →
        p ^ 4 ≤ Nat.card A → Nat.card A ≤ p ^ nontoralMaxRank (langTag t) p →
        BandRankFloor t f p A → ¬ CaseEightV t f p A →
        IsToralSubgroup (langTag t) GGL A := by
  intro t ht f hf p hp A hA hel h4 hmax hrk hv
  have hp1 : 1 < p := hp.one_lt
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    exfalso
    refine not_pow_four_le hp1 ?_ h4 hmax
    simp only [langTag, nontoralMaxRank]; split_ifs <;> omega
  ·
    by_cases hp3 : p = 3
    · subst hp3
      have hmx : nontoralMaxRank (langTag .E6) 3 = 4 := rfl
      rw [hmx] at hmax
      have hc : Nat.card A = 3 ^ 4 := le_antisymm hmax h4
      rcases Nat.even_or_odd f with he | ho
      · exfalso
        have h5 := (hrk rfl).2.1 rfl he
        rw [hc] at h5; norm_num at h5
      · exact h6c f hf .E6 (Or.inl ⟨rfl, ho⟩) A hA hel hc
    · exfalso
      refine not_pow_four_le hp1 (m := 0) (by norm_num) h4 ?_
      simpa [langTag, nontoralMaxRank, hp3] using hmax
  ·
    exfalso
    by_cases hp3 : p = 3
    · subst hp3
      have hmx : nontoralMaxRank (langTag .E7) 3 = 4 := rfl
      rw [hmx] at hmax
      have h6 := (hrk rfl).1 (Or.inl rfl)
      have hr : (langTag .E7).rank - 1 = 6 := rfl
      rw [hr] at h6
      have : 3 ^ 6 ≤ 3 ^ 4 := h6.trans hmax
      norm_num at this
    · refine not_pow_four_le hp1 (m := 0) (by norm_num) h4 ?_
      simpa [langTag, nontoralMaxRank, hp3] using hmax
  ·
    exfalso
    by_cases hp3 : p = 3
    · subst hp3
      have hmx : nontoralMaxRank (langTag .E8) 3 = 5 := rfl
      rw [hmx] at hmax
      have h7 := (hrk rfl).1 (Or.inr rfl)
      have hr : (langTag .E8).rank - 1 = 7 := rfl
      rw [hr] at h7
      have : 3 ^ 7 ≤ 3 ^ 5 := h7.trans hmax
      norm_num at this
    · by_cases hp5 : p = 5
      · subst hp5
        exact not_pow_four_le hp1 (m := 3) le_rfl h4 hmax
      · refine not_pow_four_le hp1 (m := 0) (by norm_num) h4 ?_
        simpa [langTag, nontoralMaxRank, hp3, hp5] using hmax
  ·
    by_cases hp3 : p = 3
    · subst hp3
      have hmx : nontoralMaxRank (langTag .twistedE6) 3 = 4 := rfl
      rw [hmx] at hmax
      have hc : Nat.card A = 3 ^ 4 := le_antisymm hmax h4
      rcases Nat.even_or_odd f with he | ho
      · exact h6c f hf .twistedE6 (Or.inr ⟨rfl, he⟩) A hA hel hc
      · exfalso
        have h3 := three_dvd_two_pow_add_one ho
        by_cases h9 : 9 ∣ 2 ^ f + 1
        · have h5 := (hrk rfl).2.2.1 rfl h9
          rw [hc] at h5; norm_num at h5
        · by_cases hAR : A ≤ ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆
          · exact hv ⟨rfl, rfl, h3, h9, hAR⟩
          · have h5 := (hrk rfl).2.2.2 rfl ho hAR
            rw [hc] at h5; norm_num at h5
    · exfalso
      refine not_pow_four_le hp1 (m := 0) (by norm_num) h4 ?_
      simpa [langTag, nontoralMaxRank, hp3] using hmax

end CFSG.StandardType.RCKBand
