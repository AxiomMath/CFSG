module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

public section

namespace CFSG.Quasithin.H13

namespace L1294S

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isometry_pow {B : LinearMap.BilinForm (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ v w, B (g v) (g w) = B v w) (i : ℕ) (v w : V) : B ((g ^ i) v) ((g ^ i) w) = B v w := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, ih]

theorem eq_one_of_pow_seven [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hdim : Module.finrank (ZMod 2) V = 4) {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ v w, B (g v) (g w) = B v w) (h7 : g ^ 7 = 1) : g = 1 := by
  classical
  have h7p : Nat.Prime 7 := by decide
  have : Fact (Nat.Prime 7) := ⟨h7p⟩
  have hFD : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set C : Submodule (ZMod 2) V := LinearMap.ker (g.toLinearMap - LinearMap.id) with hC
  have hmemC : ∀ v, v ∈ C ↔ g v = v := fun v => by
    simp [hC, sub_eq_zero]
  set Z := Subgroup.zpowers g with hZ
  have hZp : IsPGroup 7 Z := by
    have hdvd : orderOf g ∣ 7 := orderOf_dvd_of_pow_eq_one h7
    rcases (Nat.dvd_prime h7p).1 hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hfix : Nat.card (MulAction.fixedPoints Z V) = Nat.card C := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    show (∀ m : Z, m • v = v) ↔ v ∈ C
    rw [hmemC]
    constructor
    · intro h
      exact h ⟨g, Subgroup.mem_zpowers g⟩
    · rintro h ⟨z, k, rfl⟩
      change (g ^ k) v = v
      induction k using Int.induction_on with
      | zero => rfl
      | succ k ih => rw [zpow_add_one, LinearEquiv.mul_apply, h, ih]
      | pred k ih =>
        have hginv : g⁻¹ v = v := by
          conv_lhs => rw [← h]
          exact g.symm_apply_apply v
        rw [zpow_sub_one, LinearEquiv.mul_apply, hginv, ih]
  have hmod := hZp.card_modEq_card_fixedPoints V
  rw [hfix, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), hdim,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := C), Nat.card_zmod] at hmod
  have hCle : Module.finrank (ZMod 2) C ≤ 4 := hdim ▸ Submodule.finrank_le C
  have hk : Module.finrank (ZMod 2) C = 1 ∨ Module.finrank (ZMod 2) C = 4 := by
    have hmod' : 2 ^ 4 % 7 = 2 ^ Module.finrank (ZMod 2) C % 7 := hmod
    interval_cases h : Module.finrank (ZMod 2) C <;>
      first | exact Or.inl rfl | exact Or.inr rfl | (norm_num at hmod')
  rcases hk with hk | hk
  ·
    exfalso
    obtain ⟨c, hcC, hc0⟩ : ∃ c ∈ C, c ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot (by
        intro hb
        rw [hb, finrank_bot] at hk
        exact absurd hk (by norm_num))
    have hCc : ∀ x ∈ C, x = 0 ∨ x = c := by
      intro x hx
      have h2 : Nat.card C = 2 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hk, Nat.card_zmod, pow_one]
      by_contra hne
      push Not at hne
      have h3 : 3 ≤ Nat.card C := by
        have h3c : ({⟨0, C.zero_mem⟩, ⟨c, hcC⟩, ⟨x, hx⟩} : Finset C).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair]
          · intro h
            exact hne.2 (congrArg Subtype.val h).symm
          · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
            exact ⟨fun h => hc0 h.symm, fun h => hne.1 h.symm⟩
        have := Fintype.ofFinite C
        rw [Nat.card_eq_fintype_card]
        calc 3 = _ := h3c.symm
          _ ≤ _ := Finset.card_le_univ _
      omega
    apply hc0
    apply hnd c
    intro w
    set e : V := ∑ i ∈ Finset.range 7, (g ^ i) w with he
    have heC : e ∈ C := by
      rw [hmemC, he, map_sum]
      have hs : ∀ i, g ((g ^ i) w) = (g ^ (i + 1)) w := fun i => by
        rw [pow_succ', LinearEquiv.mul_apply]
      simp_rw [hs]
      rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun i => (g ^ i) w), h7]
      simp only [pow_zero]
    have hBe : B c e = B c w := by
      rw [he, map_sum]
      have hci : ∀ i, (g ^ i) c = c := fun i => by
        induction i with
        | zero => rfl
        | succ i ih => rw [pow_succ', LinearEquiv.mul_apply, ih, (hmemC c).1 hcC]
      have hterm : ∀ i ∈ Finset.range 7, B c ((g ^ i) w) = B c w := fun i _ => by
        conv_lhs => rw [← hci i]
        exact isometry_pow hg i c w
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
      rw [nsmul_eq_mul, show ((7 : ℕ) : ZMod 2) = 1 by decide, one_mul]
    rw [← hBe]
    rcases hCc e heC with h | h <;> rw [h]
    · exact map_zero _
    · exact halt c
  ·
    have hCtop : C = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hk, hdim])
    refine LinearEquiv.ext fun v => ?_
    have := (hmemC v).1 (hCtop ▸ Submodule.mem_top)
    rw [this]
    rfl

end L1294S

end CFSG.Quasithin.H13
