module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.KFacts

theorem exists_ne_of_sylow_of_card_dvd {X : Type*} [Group X] [Finite X] (α : MulAut X) {M : ℕ}
    (hM : ∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) (h3M : 3 * M ∣ Nat.card X)
    (S : Sylow 3 X) : ∃ y ∈ (S : Subgroup X), α y ≠ y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have h1 := hM S hcon
  rw [S.card_eq_multiplicity] at h1
  apply Nat.pow_succ_factorization_not_dvd (Nat.card_pos (α := X)).ne' Nat.prime_three
  rw [pow_succ, mul_comm]
  exact (Nat.mul_dvd_mul_left 3 h1).trans h3M

theorem isCyclic_sylow_subgroup {X : Type*} [Group X] {p : ℕ} [Fact p.Prime] (C : Subgroup X)
    (hcyc : ∀ P : Sylow p X, IsCyclic P) (P : Sylow p C) : IsCyclic P := by
  obtain ⟨S, hS⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  have := hcyc S
  have e : (P : Subgroup C) ≃* ((P : Subgroup C).map C.subtype).subgroupOf (S : Subgroup X) :=
    (Subgroup.equivMapOfInjective _ _ C.subtype_injective).trans
      (Subgroup.subgroupOfEquivOfLe hS).symm
  exact isCyclic_of_surjective e.symm e.symm.surjective

theorem exists_conj_eq_inv_of_isCyclic_sylow {X : Type*} [Group X] [Finite X] (C : Subgroup X)
    (hcyc : ∀ P : Sylow 3 X, IsCyclic P) {x₀ y₀ : X} (hx₀C : x₀ ∈ C) (hy₀C : y₀ ∈ C)
    (hx₀3 : x₀ ^ 3 = 1) (hx₀1 : x₀ ≠ 1) (hinv : y₀ * x₀ * y₀⁻¹ = x₀⁻¹) {x : X} (hxC : x ∈ C)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : ∃ y ∈ C, y * x * y⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : ∀ z : C, (z : X) ^ 3 = 1 → (z : X) ≠ 1 → orderOf z = 3 := fun z h3 h1 =>
    orderOf_eq_prime (Subtype.ext (by simpa using h3)) (fun h => h1 (by simp [h]))
  have hpg : ∀ z : C, (z : X) ^ 3 = 1 → (z : X) ≠ 1 → IsPGroup 3 (Subgroup.zpowers z) :=
    fun z h3 h1 => IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord z h3 h1, pow_one])
  obtain ⟨P, hP⟩ := (hpg ⟨x, hxC⟩ hx3 hx1).exists_le_sylow
  obtain ⟨P₀, hP₀⟩ := (hpg ⟨x₀, hx₀C⟩ hx₀3 hx₀1).exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq C P₀ P
  have hxP : (⟨x, hxC⟩ : C) ∈ g • P₀ := hP (Subgroup.mem_zpowers _)
  rw [← SetLike.mem_coe, Sylow.coe_smul] at hxP
  obtain ⟨s, hs, hsx⟩ := Set.mem_smul_set.mp hxP
  rw [MulAut.smul_def, MulAut.conj_apply] at hsx
  have hsx' : (g : X) * (s : X) * (g : X)⁻¹ = x := by
    have h := congrArg (fun z : C => (z : X)) hsx
    simpa using h
  have hx0P : (⟨x₀, hx₀C⟩ : C) ∈ (P₀ : Subgroup C) := hP₀ (Subgroup.mem_zpowers _)
  have hcyc₀ : IsCyclic (P₀ : Subgroup C) := isCyclic_sylow_subgroup C hcyc P₀
  have hord₀ : ∀ z : (P₀ : Subgroup C), ((z : C) : X) ^ 3 = 1 → ((z : C) : X) ≠ 1 →
      orderOf z = 3 := fun z h3 h1 =>
    orderOf_eq_prime (Subtype.ext (Subtype.ext (by simpa using h3)))
      (fun h => h1 (by simp [h]))
  have hs3 : (s : X) ^ 3 = 1 := by
    have h2 : ((g : X) * (s : X) * (g : X)⁻¹) ^ 3 = 1 := by rw [hsx']; exact hx3
    rw [conj_pow] at h2
    have h3 := congrArg (fun z => (g : X)⁻¹ * z * (g : X)) h2
    simpa [mul_assoc] using h3
  have hs1 : (s : X) ≠ 1 := by
    intro h1
    apply hx1
    rw [← hsx', h1, mul_one, mul_inv_cancel]
  set s' : (P₀ : Subgroup C) := ⟨s, hs⟩ with hs'
  set a₀ : (P₀ : Subgroup C) := ⟨⟨x₀, hx₀C⟩, hx0P⟩ with ha₀
  have heq : Subgroup.zpowers s' = Subgroup.zpowers a₀ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      hord₀ s' hs3 hs1, hord₀ a₀ hx₀3 hx₀1]
  have hmem : s' ∈ Subgroup.zpowers a₀ := by
    rw [← heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : x₀ ^ k = (s : X) := by
    have h := congrArg (fun z : (P₀ : Subgroup C) => ((z : C) : X)) hk
    simpa [s', a₀] using h
  refine ⟨(g : X) * y₀ * (g : X)⁻¹, C.mul_mem (C.mul_mem g.2 hy₀C) (C.inv_mem g.2), ?_⟩
  have hinvk : y₀ * x₀ ^ k * y₀⁻¹ = (x₀ ^ k)⁻¹ := by
    rw [← conj_zpow, hinv, inv_zpow]
  rw [← hsx', ← hk']
  calc (g : X) * y₀ * (g : X)⁻¹ * ((g : X) * x₀ ^ k * (g : X)⁻¹) * ((g : X) * y₀ * (g : X)⁻¹)⁻¹
      = (g : X) * (y₀ * x₀ ^ k * y₀⁻¹) * (g : X)⁻¹ := by group
    _ = ((g : X) * x₀ ^ k * (g : X)⁻¹)⁻¹ := by rw [hinvk]; group

theorem congr_trans_mulAut {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y) (γ : MulAut Y)
    (α : MulAut X) : MulAut.congr (ψ.trans γ) α = γ * MulAut.congr ψ α * γ⁻¹ := by
  ext y
  rfl

theorem fixedData_of_congr {X Y : Type*} [Group X] [Group Y] (τ : X ≃* Y) (α : MulAut X)
    (h₁ : ∃ M : ℕ, (∀ T : Subgroup Y, (∀ t ∈ T, MulAut.congr τ α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card Y)
    (h₂ : ∃ x₀ y₀ : Y, MulAut.congr τ α x₀ = x₀ ∧ MulAut.congr τ α y₀ = y₀ ∧ x₀ ^ 3 = 1 ∧
      x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹) :
    (∃ M : ℕ, (∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧ 3 * M ∣ Nat.card X) ∧
      ∃ x₀ y₀ : X, α x₀ = x₀ ∧ α y₀ = y₀ ∧ x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  have hfix : ∀ y : Y, MulAut.congr τ α y = y → α (τ.symm y) = τ.symm y := fun y hy => by
    apply τ.injective
    rw [MulEquiv.apply_symm_apply]
    exact hy
  obtain ⟨M, hM, h3M⟩ := h₁
  obtain ⟨x₀, y₀, hx₀, hy₀, hx₀3, hx₀1, hinv⟩ := h₂
  refine ⟨⟨M, fun T hT => ?_, by rwa [Nat.card_congr τ.toEquiv]⟩,
    τ.symm x₀, τ.symm y₀, hfix x₀ hx₀, hfix y₀ hy₀, by rw [← map_pow, hx₀3, map_one],
    fun h => hx₀1 (τ.symm.injective (h.trans (map_one _).symm)), ?_⟩
  · have h := hM (T.map τ.toMonoidHom) ?_
    · rwa [Subgroup.card_map_of_injective τ.injective] at h
    · rintro _ ⟨t, ht, rfl⟩
      change τ (α (τ.symm (τ t))) = τ t
      rw [MulEquiv.symm_apply_apply, hT t ht]
  · rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv]

theorem three_dvd_pow_four_add_sq_add_one {a : ℕ} (ha : a % 3 ≠ 0) : 3 ∣ a ^ 4 + a ^ 2 + 1 := by
  have h : a % 3 = 1 ∨ a % 3 = 2 := by omega
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.add_mod (a ^ 4), Nat.pow_mod, Nat.pow_mod a 2]
  rcases h with h | h <;> rw [h]

theorem three_mul_dvd_linear {a : ℕ} (ha : a % 3 ≠ 0) (ha1 : 1 ≤ a) :
    3 * (a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1))) ∣
      (a ^ 3) ^ 3 * (((a ^ 3) ^ 2 - 1) * ((a ^ 3) ^ 3 - 1)) := by
  obtain ⟨m, hm⟩ := three_dvd_pow_four_add_sq_add_one ha
  refine ⟨a ^ 6 * m * (a ^ 6 + a ^ 3 + 1), ?_⟩
  have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha1
  have h3 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ ha1
  have h6 : 1 ≤ (a ^ 3) ^ 2 := Nat.one_le_pow _ _ h3
  have h9 : 1 ≤ (a ^ 3) ^ 3 := Nat.one_le_pow _ _ h3
  have hm' : ((a : ℤ) ^ 4 + a ^ 2 + 1) = 3 * m := by exact_mod_cast hm
  zify [h2, h3, h6, h9]
  linear_combination ((a : ℤ) ^ 9 * (a ^ 2 - 1) * (a ^ 3 - 1) * (a ^ 6 + a ^ 3 + 1)) * hm'

theorem three_mul_dvd_unitary {a : ℕ} (ha : a % 3 ≠ 0) (ha1 : 1 ≤ a) :
    3 * (a ^ 3 * (a ^ 2 - 1) * (a ^ 3 + 1)) ∣
      (a ^ 3) ^ 3 * ((a ^ 3) ^ 2 - 1) * ((a ^ 3) ^ 3 + 1) := by
  obtain ⟨m, hm⟩ := three_dvd_pow_four_add_sq_add_one ha
  have h36 : a ^ 3 ≤ a ^ 6 := Nat.pow_le_pow_right ha1 (by norm_num)
  refine ⟨a ^ 6 * m * (a ^ 6 - a ^ 3 + 1), ?_⟩
  have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha1
  have h3 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ ha1
  have h6 : 1 ≤ (a ^ 3) ^ 2 := Nat.one_le_pow _ _ h3
  have hm' : ((a : ℤ) ^ 4 + a ^ 2 + 1) = 3 * m := by exact_mod_cast hm
  zify [h2, h6, h36]
  linear_combination ((a : ℤ) ^ 9 * (a ^ 2 - 1) * (a ^ 3 + 1) * (a ^ 6 - a ^ 3 + 1)) * hm'

end CFSG.RankThree.PartTwo.KFacts
