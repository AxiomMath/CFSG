module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowA5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowA5A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_center_eq_bot_of_isAlt5 {X : Type} [Group X] (h : UC22.IsAlt X 5) :
    Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  rw [eq_bot_iff]
  intro x hx
  have hxe : e x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [alternatingGroup.center_eq_bot (by norm_num)] at hxe
  exact Subgroup.mem_bot.mpr
    (e.injective ((Subgroup.mem_bot.mp hxe).trans (map_one e).symm))

private theorem s16h_not_sq_dvd_120 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ 120 := by
  intro h
  have hle : q ^ 2 ≤ 120 := Nat.le_of_dvd (by norm_num) h
  have hq2le : 2 ≤ q := hq.two_le
  have hq10 : q ≤ 10 := by nlinarith
  interval_cases q
  · exact hq2 rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

private lemma s16h_prime_dvd_168 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h : q ∣ 168) :
    q = 3 ∨ q = 7 := by
  have h168 : (168 : ℕ) = 2 ^ 3 * 3 * 7 := by norm_num
  rw [h168] at h
  rcases hq.dvd_mul.mp h with h1 | h7
  · rcases hq.dvd_mul.mp h1 with h2 | h3
    · have h2' : q ∣ 2 := hq.dvd_of_dvd_pow h2
      have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2'
      exact absurd this hq2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).mp h3)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).mp h7)

theorem s16h_H5_row_A5_one {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {k : ℕ} (hk : k ≤ 3)
    (h : s16h_H5A5Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3 ∨ k ≤ 1) : s16h_BlockBound A L q 1 := by
  have hq168 : ¬ q ∣ 168 ∨ ¬ q ∣ 120 ∨ k ≤ 1 := by
    by_cases hk1 : k ≤ 1
    · exact Or.inr (Or.inr hk1)
    · have hq3' : q ≠ 3 := by
        rcases hq3 with h3 | h3
        · exact h3
        · exact absurd h3 hk1
      by_cases hq168' : q ∣ 168
      · refine Or.inr (Or.inl ?_)
        have hq7 : q = 7 := by
          rcases s16h_prime_dvd_168 hq hq2 hq168' with h3 | h7
          · exact absurd h3 hq3'
          · exact h7
        rw [hq7]
        norm_num
      · exact Or.inl hq168'
  have hb : ∀ E : Subgroup (MulAut W), E ≤ A ⊓ normalizer (L : Set (MulAut W)) →
      IsElemAbelian q E → Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q := by
    intro E hE hEab
    rcases h with ⟨hOM, hS⟩ | ⟨hAlt, hS⟩
    · have hAlt' : UC22.IsAlt ↥L 5 := s16k_isAlt_five_of_isOmegaMinus_four hOM
      have hcenter : Subgroup.center ↥L = ⊥ := s16h_center_eq_bot_of_isAlt5 hAlt'
      have hM : Nat.card (MulAut ↥L) ∣ 120 := s16h_card_mulAut_alt5_dvd hAlt'
      exact s16h_H5_sum_glue_one hc (N := fun H U Z => NatOmegaMinus H U Z 4 1)
        (fun I hI => s16h_simpleScalar_natOmegaMinus4 hc.comp.2.2 hOM hI) hk hS hcenter hM
        hq hq2 (s16h_not_sq_dvd_120 hq hq2) hq168 E hE hEab
    · have hcenter : Subgroup.center ↥L = ⊥ := s16h_center_eq_bot_of_isAlt5 hAlt
      have hM : Nat.card (MulAut ↥L) ∣ 120 := s16h_card_mulAut_alt5_dvd hAlt
      exact s16h_H5_sum_glue_one hc (N := fun H U Z => AlternatingNatural H U Z 5)
        (fun I hI => s16h_simpleScalar_alt5 hc.comp.2.2 hAlt hI) hk hS hcenter hM
        hq hq2 (s16h_not_sq_dvd_120 hq hq2) hq168 E hE hEab
  exact s16h_H5_block_of_autSub_one hb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
