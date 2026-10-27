module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35Cases
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

section Q35


theorem s21_12aFR34F2Q35_of_kfacts (hKF1 : KFieldAutOdd) (hNS : KQ35NormSylowAlpha)
    (hPF : KQ35PermFive) {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h5 : S21_5 D Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀) :
    S21_12aFR34F2Q35 D (Choice214U D) := by
  intro hH c L hL p hp hp2 t n f hadm ht hq5 hX _ hfaith
  exfalso
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hf1 : f = 1 := by
    have hf := hadm.2.1
    by_contra hf1
    have h9 : 3 ^ 2 ≤ p ^ f :=
      (Nat.pow_le_pow_left hp3 2).trans (Nat.pow_le_pow_right hp.pos (by omega))
    norm_num at h9
    omega
  subst hf1
  have hp35 : p = 3 ∨ p = 5 := by
    rw [pow_one] at hq5
    obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
    omega
  have hn3' : 3 ≤ c.n := hn3 hH (c.mono hCh)
  have hBN : c.B0 ≤ normalizer (L : Set G) :=
    h5 hH { c.mono hCh with B := c.B0, hB := c.hB0, hle := le_rfl } L hL
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := c.n) (by omega)
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hn
    by_cases he : e ≤ 2
    · have hn4 : c.n = 4 := by
        interval_cases e <;> norm_num at hn <;> omega
      exact uc22s2112r34q35_false_four hKF1 hPF hσ hH c hn4 hL hBN hfaith hp35 hadm ht hX
    · have h8 : 8 ∣ c.n := by
        rw [hn]
        exact (by norm_num : (8 : ℕ) ∣ 2 ^ 3).trans (pow_dvd_pow 2 (by omega))
      exact uc22s2112r34q35_false_eight hKF1 c h8 hL hBN hfaith hp35 hadm ht hX
  · have hm3 : 3 ≤ m := by
      obtain ⟨k, hk⟩ := hm
      omega
    exact uc22s2112r34q35_false_alpha hKF1 hNS c hm hm3 hn hL hBN hfaith hp35 hadm ht hX

end Q35

section F2


theorem s21_12aFR34F2_of_sig_even (hKF1 : KFieldAutOdd) (hKS : KFunSplit) (hKC : KFunCount)
    (hNS : KQ35NormSylowAlpha) (hPF : KQ35PermFive) (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h5 : S21_5 D Ch) (h82 : F08.R82 D)
    (h211 : S21_1 D Ch) (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀)
    (hSg : S21_12aFR34F2Sig D (Choice214U D)) (hEv : S21_12aFR34F2Even D (Choice214U D)) :
    S21_12aFR34F2 D (Choice214U D) :=
  s21_12aFR34F2_of_cases hKF1 hKS hKC hGA hσ hKF7 hn3 h5 h82 h211 hCh
    (s21_12aFR34F2Q35_of_kfacts hKF1 hNS hPF hσ hn3 h5 hCh) hSg hEv

end F2

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
