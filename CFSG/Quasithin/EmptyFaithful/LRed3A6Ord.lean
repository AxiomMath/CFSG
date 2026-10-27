module

public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA

structure A6Target (X : Type) [Group X] : Prop where
  isSimple : IsSimpleGroup X
  noncomm : ∃ a b : X, a * b ≠ b * a
  card : Nat.card X = 360

theorem A6Target.of_isAlt {X : Type} [Group X] (h : IsAlt 6 X) : A6Target X := by
  obtain ⟨e⟩ := h
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := isSimpleGroup_alt (n := 6) (by norm_num)
  refine ⟨e.isSimpleGroup, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.Bridge.alt_exists_noncomm (m := 6) (by norm_num)
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  · rw [Nat.card_congr e.toEquiv, card_alt 6 (by norm_num)]
    decide

theorem A6Target.finite {X : Type} [Group X] (h : A6Target X) : Finite X :=
  Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)

theorem A6Target.nontrivial {X : Type} [Group X] (h : A6Target X) : Nontrivial X := by
  have := h.finite
  exact Finite.one_lt_card_iff_nontrivial.mp (by rw [h.card]; norm_num)

theorem lred3_false_of_simple {Γ X : Type} [Group Γ] [Group X] (hX : A6Target X)
    (hΓ : IsSimpleGroup Γ) (hc : Nat.card Γ ≠ 360) (π : Γ →* X) (hπ : Function.Surjective π) :
    False := by
  have := hX.nontrivial
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective hΓ π hπ
  exact hc (by rw [Nat.card_congr e.toEquiv, hX.card])

theorem lred3_odd_four_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (4 ^ n - 1) := by
  have h : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  rw [h]
  exact odd_two_pow_sub_one (by omega)

theorem lred3_360 : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num

theorem lred3_sl2_ne_360 {n : ℕ} (hn : 1 ≤ n) (h : 2 ^ n * (4 ^ n - 1) = 360) : False := by
  obtain ⟨hn3, h45⟩ := two_pow_mul_odd_inj (lred3_odd_four_pow_sub_one hn) (by decide : Odd 45)
    (h.trans lred3_360)
  subst hn3
  norm_num at h45

theorem lred3_sl3_ne_360 {n : ℕ} (hn : 1 ≤ n)
    (h : 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) = 360) : False := by
  have hodd : Odd ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) :=
    (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  obtain ⟨hn3, h45⟩ := two_pow_mul_odd_inj hodd (by decide : Odd 45) (h.trans lred3_360)
  have : n = 1 := by omega
  subst this
  norm_num at h45

theorem lred3_sp4_ne_360 {n : ℕ} (hn : 1 ≤ n)
    (h : 2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) = 360) : False := by
  have hodd : Odd ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) :=
    (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  obtain ⟨hn3, -⟩ := two_pow_mul_odd_inj hodd (by decide : Odd 45) (h.trans lred3_360)
  omega

theorem lred3_suzuki_ne_360 {a : ℕ}
    (h : (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) = 360) :
    False := by
  have heven : Even (2 ^ (2 * a + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hodd : Odd ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) :=
    (odd_two_pow_sub_one (by omega)).mul (Nat.even_pow.mpr ⟨heven, two_ne_zero⟩).add_one
  have h2 : 2 ^ (2 * (2 * a + 1)) = (2 ^ (2 * a + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
  have h' : 2 ^ (2 * (2 * a + 1)) * ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) = 360 := by
    rw [h2, ← mul_assoc]
    exact h
  obtain ⟨h1, -⟩ := two_pow_mul_odd_inj hodd (by decide : Odd 45) (h'.trans lred3_360)
  omega

theorem lred3_le_three_of_two_pow_dvd {k : ℕ} (h : 2 ^ k ∣ 360) : k ≤ 3 := by
  by_contra hk
  have h4 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
  have := h4.trans h
  norm_num at this

end CFSG.Quasithin
