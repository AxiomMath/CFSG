module

public import CFSG.Quasithin.EmptyFaithful.T1531O4Syl
public import CFSG.Quasithin.EmptyFaithful.S152O4Model

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S152O

theorem sq_eq_one_of_nondeg {V : Type*} [Group V] {q : V → ZMod 2} (hq : IsQuadraticFormOn q)
    (hn : IsNondegQuadratic q) (x : V) : x * x = 1 := by
  refine hn (x * x) fun y => ?_
  rw [hq.2.1]
  exact CharTwo.add_self_eq_zero _

theorem sl2_cases_aux : ∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    M = 1 ∨ (M ^ 2 = 1 ∧ M ≠ 1) ∨ (M ^ 3 = 1 ∧ M ≠ 1) := by
  decide +kernel

section Natural

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {U : Subgroup W}

theorem eq_one_or_invol_or_cube (hN : ActsAsNaturalL2 L U) {m : MulAut W} (hm : m ∈ L) :
    m = 1 ∨ (m ^ 2 = 1 ∧ m ≠ 1) ∨ (m ^ 3 = 1 ∧ m ≠ 1) := by
  obtain ⟨e, -, -⟩ := hN
  have hlift : ∀ n : ℕ, e ⟨m, hm⟩ ^ n = 1 → m ^ n = 1 := fun n h => by
    have : (⟨m, hm⟩ : L) ^ n = 1 := e.injective (by rw [map_pow, h, map_one])
    exact congrArg Subtype.val this
  have hne : e ⟨m, hm⟩ ≠ 1 → m ≠ 1 := fun h h' => h (by
    have : (⟨m, hm⟩ : L) = 1 := Subtype.ext h'
    rw [this, map_one])
  rcases sl2_cases_aux (e ⟨m, hm⟩) with h | ⟨h2, h1⟩ | ⟨h3, h1⟩
  · left
    have : (⟨m, hm⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · exact Or.inr (Or.inl ⟨hlift 2 h2, hne h1⟩)
  · exact Or.inr (Or.inr ⟨hlift 3 h3, hne h1⟩)

theorem rk_eq_of_card_eq [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) {H : Subgroup W} {n : ℕ}
    (h : Nat.card H = 2 ^ n) : rk H = n := by
  have := card_eq_two_pow hexp H
  rw [h] at this
  exact (Nat.pow_right_injective le_rfl this).symm

theorem rk_fix_natural [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) (hN : ActsAsNaturalL2 L U)
    (hst : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) {m : MulAut W} (hm : m ∈ L) :
    (m = 1 → rk ↥(U ⊓ fixV (Subgroup.zpowers m)) = 2) ∧
    (m ^ 2 = 1 → m ≠ 1 → rk ↥(U ⊓ fixV (Subgroup.zpowers m)) = 1) ∧
    (m ^ 3 = 1 → m ≠ 1 → rk ↥(U ⊓ fixV (Subgroup.zpowers m)) = 0) := by
  refine ⟨fun h1 => ?_, fun h2 h1 => ?_, fun h3 h1 => ?_⟩
  · subst h1
    have : fixV (Subgroup.zpowers (1 : MulAut W)) = ⊤ := by
      refine eq_top_iff.mpr fun v _ => ?_
      rw [mem_fixV_zpowers_iff]
      simp
    rw [this, inf_top_eq]
    exact rk_eq_of_card_eq hexp (by rw [(card_of_actsAsNaturalL2 hN).2]; norm_num)
  · obtain ⟨a, haU, ha1, hfix⟩ := exists_fixed_vector hN hst hm h2 h1
    have haf : m a = a := (hfix a haU).mpr (Or.inr rfl)
    have hC : U ⊓ fixV (Subgroup.zpowers m) = Subgroup.zpowers a := by
      apply le_antisymm
      · intro u hu
        obtain ⟨hu, hfu⟩ := Subgroup.mem_inf.mp hu
        rw [mem_fixV_zpowers_iff] at hfu
        rcases (hfix u hu).mp hfu with rfl | rfl
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_zpowers _
      · exact Subgroup.zpowers_le.mpr ⟨haU, mem_fixV_zpowers_iff.mpr haf⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hC]
    exact rk_eq_of_card_eq hexp (by rw [Nat.card_zpowers, orderOf_eq_prime (hexp a) ha1, pow_one])
  · have hC : U ⊓ fixV (Subgroup.zpowers m) = ⊥ := by
      refine eq_bot_iff.mpr fun u hu' => ?_
      obtain ⟨hu, hfu⟩ := Subgroup.mem_inf.mp hu'
      rw [mem_fixV_zpowers_iff] at hfu
      rw [Subgroup.mem_bot]
      by_contra hu1
      exact h1 (eq_one_of_odd_of_fixed hN hst hm (odd_of_pow_three h3) hu hu1 hfu)
    rw [hC]
    exact rk_bot

theorem rk_fix_class [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) (hN : ActsAsNaturalL2 L U)
    (hst : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) {m : MulAut W} (hm : m ∈ L) :
    ((m ^ 2 = 1 ∧ m ≠ 1) ↔ rk ↥(U ⊓ fixV (Subgroup.zpowers m)) = 1) ∧
      rk ↥(U ⊓ fixV (Subgroup.zpowers m)) ≤ 2 := by
  obtain ⟨a1, a2, a3⟩ := rk_fix_natural hexp hN hst hm
  rcases eq_one_or_invol_or_cube hN hm with h | ⟨h2, h1⟩ | ⟨h3, h1⟩
  · have := a1 h
    exact ⟨⟨fun ⟨_, h1⟩ => absurd h h1, fun h' => by omega⟩, by omega⟩
  · have := a2 h2 h1
    exact ⟨⟨fun _ => this, fun _ => ⟨h2, h1⟩⟩, by omega⟩
  · have := a3 h3 h1
    refine ⟨⟨fun ⟨h2, h1'⟩ => absurd ?_ h1', fun h' => by omega⟩, by omega⟩
    calc m = m ^ 3 * (m ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp

end Natural

section Product

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem fixV_mul_eq (hS : OfourStruct X L₁ L₂ t) {m₁ m₂ : MulAut W} (hm₁ : m₁ ∈ L₁)
    (hm₂ : m₂ ∈ L₂) :
    fixV (Subgroup.zpowers (m₁ * m₂)) =
      (commV L₁ ⊓ fixV (Subgroup.zpowers m₁)) ⊔ (commV L₂ ⊓ fixV (Subgroup.zpowers m₂)) :=
  CFSG.Quasithin.T1531O4.fixV_mul_eq hS hm₁ hm₂

theorem rk_fixV_mul [Finite W] (hS : OfourStruct X L₁ L₂ t) {m₁ m₂ : MulAut W} (hm₁ : m₁ ∈ L₁)
    (hm₂ : m₂ ∈ L₂) :
    rk (fixV (Subgroup.zpowers (m₁ * m₂))) =
      rk ↥(commV L₁ ⊓ fixV (Subgroup.zpowers m₁)) + rk ↥(commV L₂ ⊓ fixV (Subgroup.zpowers m₂)) :=
  CFSG.Quasithin.T1531O4.rk_fixV_mul hS hm₁ hm₂

theorem even_rk_mul_iff [Finite W] (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    (hrk : rk W = 4) {m₁ m₂ : MulAut W} (hm₁ : m₁ ∈ L₁) (hm₂ : m₂ ∈ L₂) :
    Even (rk (commV (Subgroup.zpowers (m₁ * m₂)))) ↔
      ((m₁ ^ 2 = 1 ∧ m₁ ≠ 1) ↔ (m₂ ^ 2 = 1 ∧ m₂ ≠ 1)) := by
  have hsum := rk_commV_add_rk_fixV (m₁ * m₂)
  rw [rk_fixV_mul hS hm₁ hm₂, hrk] at hsum
  obtain ⟨h1, h1'⟩ := rk_fix_class hexp hS.nat₁ (fun l hl u hu => commV_stable L₁ hl hu) hm₁
  obtain ⟨h2, h2'⟩ := rk_fix_class hexp hS.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hm₂
  rw [Nat.even_iff, h1, h2]
  omega

end Product

end S152O

end CFSG.Quasithin
