module

public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Quasithin Matrix

theorem card_alt7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem card_alt6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem card_alt5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

abbrev IsA7Order (Y : Type) [Group Y] : Prop := Nat.card Y = 2520 ∨ Nat.card Y = 7560

theorem card_of_central_quot {X Y : Type} [Group X] [Group Y] [Finite X]
    (hX : IsAlt 7 X ∨ IsHat X ↥(alternatingGroup (Fin 7))) (π : X →* Y)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X) : IsA7Order Y := by
  have hY : Nat.card Y * Nat.card π.ker = Nat.card X := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker).symm
  rcases hX with hA | ⟨-, hz, ⟨e⟩⟩
  · obtain ⟨e⟩ : Nonempty (X ≃* ↥(alternatingGroup (Fin 7))) := hA
    have hc : Subgroup.center X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : e x ∈ Subgroup.center ↥(alternatingGroup (Fin 7)) := by
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro g
        obtain ⟨y, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, hx y]
      rw [alternatingGroup.center_eq_bot (by simp)] at h1
      exact Subgroup.mem_bot.mpr (e.injective (by rw [Subgroup.mem_bot.mp h1, map_one]))
    have hk : π.ker = ⊥ := le_bot_iff.mp (hc ▸ hker)
    rw [hk, Subgroup.card_bot, mul_one, Nat.card_congr e.toEquiv, card_alt7] at hY
    exact Or.inl hY
  · have hX : Nat.card X = 7560 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
        Nat.card_congr e.toEquiv, card_alt7, hz]
    have hd : Nat.card π.ker ∣ 3 := by
      rw [← hz]
      exact Subgroup.card_dvd_of_le hker
    have h3 : Nat.card π.ker = 1 ∨ Nat.card π.ker = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp hd
    rw [hX] at hY
    rcases h3 with h3 | h3 <;> rw [h3] at hY <;> omega

theorem eq_three_of_isA7Order {Y : Type} [Group Y] (hY : IsA7Order Y) {k m : ℕ} (hm : Odd m)
    (h : Nat.card Y = 2 ^ k * m) : k = 3 := by
  rcases hY with h' | h'
  · exact (SecA.eq_of_two_pow_mul_odd (a := 3) (m := 315) (by decide) hm (by omega)).symm
  · exact (SecA.eq_of_two_pow_mul_odd (a := 3) (m := 945) (by decide) hm (by omega)).symm

theorem five_dvd_of_isA7Order {Y : Type} [Group Y] (hY : IsA7Order Y) : 5 ∣ Nat.card Y := by
  rcases hY with h | h <;> rw [h] <;> norm_num

theorem seven_dvd_of_isA7Order {Y : Type} [Group Y] (hY : IsA7Order Y) : 7 ∣ Nat.card Y := by
  rcases hY with h | h <;> rw [h] <;> norm_num

theorem one_le_of_card_field {K : Type} [Field K] [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a) :
    1 ≤ a := by
  rcases Nat.eq_zero_or_pos a with rfl | h
  · have := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at this
    omega
  · exact h

theorem not_sl2 {Y : Type} [Group Y] (hY : IsA7Order Y) {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (e : Y ≃* SpecialLinearGroup (Fin 2) K) : False := by
  have h := Nat.card_congr e.toEquiv
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK, ← pow_mul] at h
  have ha := one_le_of_card_field hK
  have h3 := eq_three_of_isA7Order hY (SecA.odd_two_pow_sub_one (by omega)) h
  subst h3
  rcases hY with h' | h' <;> rw [h'] at h <;> norm_num at h

theorem not_sl3 {Y : Type} [Group Y] (hY : IsA7Order Y) {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (e : Y ≃* SpecialLinearGroup (Fin 3) K) : False := by
  have h := Nat.card_congr e.toEquiv
  have ha := one_le_of_card_field hK
  obtain ⟨m, hm, hc⟩ := SecA.card_SL3_eq ha hK
  rw [hc] at h
  have h3 := eq_three_of_isA7Order hY hm h
  have ha1 : a = 1 := by omega
  subst ha1
  have h' := Nat.card_congr e.toEquiv
  rw [CFSG.BrauerLinearThree.card_SL_three, hK] at h'
  rcases hY with h'' | h'' <;> rw [h''] at h' <;> norm_num at h'

theorem not_sp4 {Y : Type} [Group Y] (hY : IsA7Order Y) {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (e : Y ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K)) : False := by
  have h := Nat.card_congr e.toEquiv
  obtain ⟨m, hm, hc⟩ := SecA.card_Sp4_eq (one_le_of_card_field hK) hK
  rw [hc] at h
  have := eq_three_of_isA7Order hY hm h
  omega

theorem not_g2 {Y : Type} [Group Y] (hY : IsA7Order Y) {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) (e : Y ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) : False := by
  have h := Nat.card_congr e.toEquiv
  have ha := one_le_of_card_field hK
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · have ha1 : a = 1 := by omega
    subst ha1
    have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    have hd : Nat.card Y ∣ Nat.card ↥(quasithinG2 K) := by
      rw [h]
      exact Subgroup.card_dvd_of_le (Subgroup.commutator_le_self _)
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      KGNat.card_cayleyGroup, hK] at hd
    have h5 := (five_dvd_of_isA7Order hY).trans hd
    norm_num at h5
  · obtain ⟨m, hm, hc⟩ := SecA.card_G2_eq KGNat.factG2DerivedOrder_holds ha2 hK
    rw [hc] at h
    have := eq_three_of_isA7Order hY hm h
    omega

theorem not_threeA6 {Y : Type} [Group Y] [Finite Y] (hY : IsA7Order Y)
    (hz : Nat.card (Subgroup.center Y) = 3)
    (e : Y ⧸ Subgroup.center Y ≃* ↥(alternatingGroup (Fin 6))) : False := by
  have h : Nat.card Y = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y),
      Nat.card_congr e.toEquiv, card_alt6, hz]
  have h7 := seven_dvd_of_isA7Order hY
  rw [h] at h7
  norm_num at h7

theorem not_alt_five_six {Y : Type} [Group Y] (hY : IsA7Order Y) {m : ℕ} (hm : m = 5 ∨ m = 6)
    (e : Y ≃* ↥(alternatingGroup (Fin m))) : False := by
  have h := Nat.card_congr e.toEquiv
  have h7 := seven_dvd_of_isA7Order hY
  rw [h] at h7
  rcases hm with rfl | rfl
  · rw [card_alt5] at h7
    norm_num at h7
  · rw [card_alt6] at h7
    norm_num at h7

theorem card_sl_zmod_two {m : ℕ} (hm : m = 4 ∨ m = 5) :
    Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) = 20160 ∨
      Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) = 9999360 := by
  rcases hm with rfl | rfl
  · left
    rw [Matrix.card_SL_field]
    simp [Fin.prod_univ_four, ZMod.card]
  · right
    rw [Matrix.card_SL_field]
    simp [Fin.prod_univ_five, ZMod.card]

theorem not_sl_zmod_two {Y : Type} [Group Y] (hY : IsA7Order Y) {m : ℕ} (hm : m = 4 ∨ m = 5)
    (e : Y ≃* SpecialLinearGroup (Fin m) (ZMod 2)) : False := by
  have h := Nat.card_congr e.toEquiv
  rcases card_sl_zmod_two hm with h' | h' <;> rw [h'] at h <;>
    rcases hY with h'' | h'' <;> omega

end CFSG.Quasithin.Vol2.Ch11.O10
