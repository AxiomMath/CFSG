module

public import CFSG.Quasithin.Vol2.Ch11SecA02Recog
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open CFSG.Quasithin.Vol2.Ch11.SecA

namespace Sec121

theorem card_SL_two_ne {a : ℕ} (ha : 2 ≤ a) (N : ℕ)
    (hN : N = 360 ∨ N = 2520 ∨ N = 20160 ∨ N = 9999360) : 2 ^ (2 * a) * oSL2 (2 * a) ≠ N := by
  intro h
  by_cases h4 : 4 ≤ a
  · have h1 : 2 ^ 8 ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 16 ≤ 2 ^ (2 * (2 * a)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 8 * (2 ^ 16 - 1) ≤ 2 ^ (2 * a) * oSL2 (2 * a) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
    omega
  · interval_cases a <;> norm_num [oSL2] at h <;> omega

theorem one_le_of_card_field {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at this
    exact absurd this (lt_irrefl 1)
  · exact h

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_SL_four_two : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [OrderReductions.LinearOrders.card_specialLinear (ZMod 2) 4 (by norm_num), Nat.card_zmod]
  decide

theorem not_binaryOrthogonalFour {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {a : ℕ}
    (ha : 1 < a) (hO : BinaryOrthogonalFour H ⊤ ⊥ a)
    (hX : (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
        (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥H ≃* ↥(StatedSp 2 K))) ∨
        Nonempty (↥H ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
        Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
        Nonempty (↥H ≃* alternatingGroup (Fin 7))) : False := by
  obtain ⟨K, _, _, _, hK, π, hπ⟩ := hO
  have hsimp : IsSimpleGroup (FFModel.twistTensor a (StatedSL 2 K)).Gam :=
    isSimpleGroup_statedSL (isSimpleGroup_SL_two hK (by omega))
  have hcardSL : Nat.card ↥(StatedSL 2 K) = 2 ^ (2 * a) * oSL2 (2 * a) := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv, card_SL_two hK]
  have hH : Nat.card H = 2 ^ (2 * a) * oSL2 (2 * a) ∨ Nat.card H = 1 := by
    rcases (MonoidHom.normal_ker π).eq_bot_or_eq_top with hk | hk
    · left
      rw [← hcardSL]
      exact (Nat.card_congr
        (MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp hk, hπ.1⟩).toEquiv).symm
    · right
      have h1 : ∀ x : ↥H, x = 1 := fun x => by
        obtain ⟨γ, rfl⟩ := hπ.1 x
        exact MonoidHom.mem_ker.mp (hk ▸ Subgroup.mem_top γ)
      exact Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => (h1 x).trans (h1 y).symm⟩, ⟨1⟩⟩
  have hpos : 2 ≤ 2 ^ (2 * a) * oSL2 (2 * a) := by
    have : Nontrivial ↥(StatedSL 2 K) := hsimp.toNontrivial
    rw [← hcardSL]
    exact Finite.one_lt_card
  have hnum : ∀ N : ℕ, (N = 360 ∨ N = 2520 ∨ N = 20160 ∨ N = 9999360) → Nat.card H ≠ N := by
    intro N hN hHN
    rcases hH with h | h
    · exact card_SL_two_ne (by omega) N hN (h.symm.trans hHN)
    · rw [h] at hHN
      omega
  rcases hX with ⟨n, K', _, _, hK', he⟩ | ⟨n, K', _, _, hK', he⟩ | he | he | he | he
  ·
    obtain ⟨e⟩ := he
    have hn := one_le_of_card_field hK'
    have hc : Nat.card H = 2 ^ (3 * n) * oSL3 n := by
      rw [Nat.card_congr e.toEquiv, card_SL_three' hK']
    rcases hH with h | h
    · rw [h] at hc
      obtain ⟨h1, h2⟩ := two_pow_eq_of odd_one odd_one (odd_oSL3 hn)
        (odd_oSL2 (m := 2 * a) (by omega))
        (by rw [one_mul, one_mul]; exact hc)
      rw [one_mul, one_mul, h1] at h2
      exact not_dvd_oSL2_oSL3 hn (h2 ▸ dvd_refl _)
    · rw [h] at hc
      have : 2 ≤ 2 ^ (3 * n) * oSL3 n :=
        le_trans (by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega))
          (Nat.le_mul_of_pos_right _ (odd_oSL3 hn).pos)
      omega
  ·
    obtain ⟨e⟩ := he
    have hn := one_le_of_card_field hK'
    have hc : Nat.card H = 2 ^ (4 * n) * oSp4 n := by
      rw [Nat.card_congr e.toEquiv, card_Sp_four hK']
    rcases hH with h | h
    · rw [h] at hc
      obtain ⟨h1, h2⟩ := two_pow_eq_of odd_one odd_one (odd_oSp4 hn)
        (odd_oSL2 (m := 2 * a) (by omega))
        (by rw [one_mul, one_mul]; exact hc)
      rw [one_mul, one_mul, h1] at h2
      exact not_dvd_oSL2_oSp4 hn (h2 ▸ dvd_refl _)
    · rw [h] at hc
      have : 2 ≤ 2 ^ (4 * n) * oSp4 n :=
        le_trans (by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega))
          (Nat.le_mul_of_pos_right _ (odd_oSp4 hn).pos)
      omega
  · obtain ⟨e⟩ := he
    exact hnum 360 (Or.inl rfl) (by rw [Nat.card_congr e.toEquiv, card_alt_six])
  · obtain ⟨e⟩ := he
    exact hnum 20160 (Or.inr (Or.inr (Or.inl rfl)))
      (by rw [Nat.card_congr e.toEquiv, card_SL_four_two])
  · obtain ⟨e⟩ := he
    exact hnum 9999360 (Or.inr (Or.inr (Or.inr rfl)))
      (by rw [Nat.card_congr e.toEquiv, card_SL_five_two]; norm_num)
  · obtain ⟨e⟩ := he
    exact hnum 2520 (Or.inr (Or.inl rfl)) (by rw [Nat.card_congr e.toEquiv, card_alt_seven])

end Sec121

end CFSG.Quasithin.H13
