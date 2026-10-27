module

import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.H13.NQCatLieOverRank2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.H13.NQCat
open Matrix

theorem card_of_isPSL_two_two {Y : Type} [Group Y] {m : ℕ} (h : IsPSL 2 2 m Y) :
    1 ≤ m ∧ Nat.card Y = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  obtain ⟨⟨-, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hm hK
  refine ⟨hm, ?_⟩
  rw [Nat.card_congr (e.trans Vol2Native.A312L.sl2EquivStatedProj.symm).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]

theorem mul_sq_sub_one_lt {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) :
    x * (x ^ 2 - 1) < y * (y ^ 2 - 1) := by
  have h1 : x ^ 2 - 1 ≤ y ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy.le 2) 1
  have h2 : 0 < y ^ 2 - 1 := by
    have : 4 ≤ y ^ 2 := by nlinarith
    omega
  calc x * (x ^ 2 - 1) ≤ x * (y ^ 2 - 1) := Nat.mul_le_mul_left x h1
    _ < y * (y ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hxy h2

theorem eq_of_card_psl {m n : ℕ} (h : 2 ^ m * ((2 ^ m) ^ 2 - 1) = 2 ^ n * ((2 ^ n) ^ 2 - 1)) :
    m = n := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine Nat.pow_right_injective le_rfl ?_
  rcases lt_trichotomy (2 ^ m) (2 ^ n) with hlt | heq | hgt
  · exact absurd h (mul_sq_sub_one_lt h1 hlt).ne
  · exact heq
  · exact absurd h (mul_sq_sub_one_lt h2 hgt).ne'

theorem eq_of_isPSL_of_equiv_sl2 {Y : Type} [Group Y] {m n : ℕ} (h : IsPSL 2 2 m Y) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) (e : Y ≃* SpecialLinearGroup (Fin 2) K) :
    m = n := by
  obtain ⟨-, hc⟩ := card_of_isPSL_two_two h
  rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    at hc
  exact eq_of_card_psl hc.symm

theorem three_dvd_card_of_isPSL {Y : Type} [Group Y] {m : ℕ} (h : IsPSL 2 2 m Y) :
    3 ∣ Nat.card Y :=
  CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two h

theorem not_isPSL_modO2_bot {X : Type} [Group X] {B : Subgroup X} (hB : B = ⊥) {m : ℕ} :
    ¬ IsPSL 2 2 m (ModO2 B) := by
  intro h
  subst hB
  obtain ⟨hm, hc⟩ := card_of_isPSL_two_two h
  have h1 : Nat.card (ModO2 (⊥ : Subgroup X)) ∣ 1 := by
    have := Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥(⊥ : Subgroup X))
    rwa [Subgroup.card_bot] at this
  rw [hc, Nat.dvd_one] at h1
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h3 : 1 ≤ (2 ^ m) ^ 2 - 1 := by
    have : 4 ≤ (2 ^ m) ^ 2 := by nlinarith
    omega
  have : 2 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := le_mul_of_le_of_one_le h2 h3
  omega

theorem not_isPSL_of_card_168 {X : Type} [Group X] [Finite X] (hX : Nat.card X = 168)
    (P : Subgroup X) {m : ℕ} (hm : 2 ≤ m) : ¬ IsPSL 2 2 m (ModO2 (perfectCore P)) := by
  intro h
  obtain ⟨-, hc⟩ := card_of_isPSL_two_two h
  have hd : 2 ^ m * ((2 ^ m) ^ 2 - 1) ∣ 168 := by
    rw [← hc, ← hX]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · have : m = 2 := by omega
    subst this
    norm_num at hd
  · have h8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := rfl
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h3
    have h63 : 63 ≤ (2 ^ m) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ m) ^ 2 := by nlinarith
      omega
    have := Nat.le_of_dvd (by norm_num) hd
    nlinarith

@[expose] def LeviParam {X : Type} [Group X] (R : ℕ → Prop) (P : Subgroup X) : Prop :=
  perfectCore P = ⊥ ∨ ∃ (T : Type) (_ : Group T) (_ : Finite T) (_ : IsSimpleGroup T),
    (∃ a b : T, a * b ≠ b * a) ∧ (∀ m, IsPSL 2 2 m T → R m) ∧
      ∃ g : ↥(perfectCore P) →* T, Function.Surjective g ∧ IsPGroup 2 g.ker

theorem LeviParam.of_sl2 {X : Type} [Group X] {R : ℕ → Prop} {P : Subgroup X} {K : Type}
    [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hR : R n)
    (g : ↥(perfectCore P) →* SpecialLinearGroup (Fin 2) K) (hg : Function.Surjective g)
    (hker : IsPGroup 2 g.ker) : LeviParam R P := by
  have hK4 := exists_finset_card_four_of_card hn hK
  have := Vol2Native.A312L.sl2_isSimple hK4
  refine Or.inr ⟨SpecialLinearGroup (Fin 2) K, inferInstance, inferInstance, inferInstance,
    Vol2Native.A312L.sl2_nonabelian hK4, fun m hm => ?_, g, hg, hker⟩
  rw [eq_of_isPSL_of_equiv_sl2 hm hK (MulEquiv.refl _)]
  exact hR

theorem LeviParam.of_three {X : Type} [Group X] {R : ℕ → Prop} {P : Subgroup X} {T : Type}
    [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    (h3 : ¬ 3 ∣ Nat.card T) (g : ↥(perfectCore P) →* T) (hg : Function.Surjective g)
    (hker : IsPGroup 2 g.ker) : LeviParam R P :=
  Or.inr ⟨T, inferInstance, inferInstance, inferInstance, hnab,
    fun _ hm => absurd (three_dvd_card_of_isPSL hm) h3, g, hg, hker⟩

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
