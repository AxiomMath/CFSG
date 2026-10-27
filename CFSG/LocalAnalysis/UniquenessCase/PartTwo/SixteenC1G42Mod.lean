module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1F431Kit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Mod

theorem s16c1G_quad_one {W : Type*} [CommGroup W] {Q : W → ZMod 2} (hQ : IsQuadF2 Q) :
    Q 1 = 0 := by
  have h := hQ.1 1 1 1
  simp only [polarQ, mul_one] at h
  have key : ∀ a : ZMod 2, a - a - a = (a - a - a) + (a - a - a) → a = 0 := by
    decide
  exact key (Q 1) h

theorem s16c1G_exists_const_of_fixed {W : Type*} [CommGroup W] [Finite W] (φ : MulAut W)
    {A : Subgroup W} (hA : Nat.card W ≤ 2 * Nat.card A) (hfix : ∀ a ∈ A, φ a = a) :
    ∃ c : W, ∀ w : W, φ w = w ∨ φ w = w * c := by
  have hcard := Subgroup.card_mul_index A
  haveI : Nonempty A := ⟨1⟩
  have hpos : 0 < Nat.card A := Nat.card_pos
  haveI : Nonempty W := ⟨1⟩
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hidx_pos : 0 < A.index := by
    by_contra h
    have h0 : A.index = 0 := Nat.eq_zero_of_not_pos h
    rw [h0, mul_zero] at hcard
    omega
  have hidx_le : A.index ≤ 2 := by
    have h : Nat.card A * A.index ≤ Nat.card A * 2 := by
      calc Nat.card A * A.index = Nat.card W := hcard
        _ ≤ 2 * Nat.card A := hA
        _ = Nat.card A * 2 := by ring
    exact Nat.le_of_mul_le_mul_left h hpos
  rcases (by omega : A.index = 1 ∨ A.index = 2) with h1 | h2
  · refine ⟨1, fun w => Or.inl ?_⟩
    have htop : A = ⊤ := Subgroup.index_eq_one.mp h1
    exact hfix w (by rw [htop]; exact Subgroup.mem_top w)
  · obtain ⟨a, _ha, hamem⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp h2
    refine ⟨a * (φ a)⁻¹, fun w => ?_⟩
    by_cases hw : w ∈ A
    · exact Or.inl (hfix w hw)
    · right
      have hwa : w * a ∈ A := (hamem w).resolve_right hw
      have h1 : φ w * φ a = w * a := by
        simpa only [map_mul] using hfix (w * a) hwa
      calc φ w = (φ w * φ a) * (φ a)⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = (w * a) * (φ a)⁻¹ := by rw [h1]
        _ = w * (a * (φ a)⁻¹) := by rw [mul_assoc]

theorem s16c1G_card_le_of_singular_commutator {W : Type} [CommGroup W] [Finite W]
    (hW : Nat.card W = 64) {H : Subgroup (MulAut W)} (hnt : OmegaNoTrans H)
    (hout : OmegaOuterNons H) {Q : W → ZMod 2} (hQ : IsMinusQuadF2 Q) (hQi : QuadInvariant Q H)
    {g : MulAut W} (hg : g ∈ normalizer (H : Set (MulAut W))) {w : W} (hw : g w * w⁻¹ ≠ 1)
    (hsing : Q (g w * w⁻¹) = 0) {A : Subgroup W} (hA : ∀ a ∈ A, g a = a) :
    Nat.card A ≤ 16 := by
  by_contra hle
  have hgt : 16 < Nat.card A := not_le.1 hle
  have hdvd : Nat.card A ∣ 64 := by
    rw [← hW]
    exact Subgroup.card_subgroup_dvd_card A
  have hdvd' : Nat.card A ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num]
    exact hdvd
  obtain ⟨k, hk6, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 6)).1 hdvd'
  have hk5 : 5 ≤ k := by
    by_contra h
    have hk4 : k ≤ 4 := by omega
    have hpow : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
    norm_num at hpow
    omega
  have hA32 : Nat.card A = 32 ∨ Nat.card A = 64 := by
    interval_cases k <;> (norm_num at hk; omega)
  have hcardW_le : Nat.card W ≤ 2 * Nat.card A := by
    rcases hA32 with h | h <;> omega
  obtain ⟨c, hc⟩ := s16c1G_exists_const_of_fixed g hcardW_le hA
  have hgw_ne : g w ≠ w := fun h => hw (by rw [h, mul_inv_cancel])
  have hgwc : g w = w * c := by
    rcases hc w with h | h
    · exact absurd h hgw_ne
    · exact h
  have hc_eq : c = g w * w⁻¹ := by
    rw [hgwc, mul_assoc, mul_comm c w⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hc_ne : c ≠ 1 := by rw [hc_eq]; exact hw
  have hcQ : Q c = 0 := by rw [hc_eq]; exact hsing
  by_cases hgH : g ∈ H
  · have hg1 : g = 1 := hnt g hgH c hc_ne (fun x => hc x)
    rw [hg1] at hgw_ne
    simpa using hgw_ne
  · obtain ⟨x, hx⟩ := hout Q hQ hQi g hg hgH
    rcases hc x with h | h
    · apply hx
      rw [h, mul_inv_cancel]
      exact s16c1G_quad_one hQ.1.1
    · apply hx
      have hxc : g x * x⁻¹ = c := by
        rw [h, mul_assoc, mul_comm c x⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [hxc, hcQ]

theorem s16c1G_rk_le_two {W : Type} [CommGroup W] [Finite W] (hW : rk (⊤ : Subgroup W) = 6)
    (hsq : ∀ x : W, x * x = 1) {Q : W → ZMod 2} (hQ : IsMinusQuadF2 Q) {A : Subgroup W}
    (hA : ∀ a ∈ A, Q a = 0) : rk ↥A ≤ 2 := by
  have h := two_mul_rk_lt_of_totallySingular_minus hsq hQ A hA
  omega

end Mod

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
