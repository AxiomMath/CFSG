module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.Timmesfeld.Transvection.QuadForm

open QuadraticMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem apply_smul_add_smul (Q : QuadraticForm K V) (a b : K) (x y : V) :
    Q (a • x + b • y) = a * a * Q x + b * b * Q y + a * b * polar Q x y := by
  rw [QuadraticMap.map_add (⇑Q) (a • x) (b • y), QuadraticMap.map_smul, QuadraticMap.map_smul,
    polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    mul_assoc a b]

section CharTwo

variable [CharP K 2]

@[simp]
theorem polar_self_eq_zero (Q : QuadraticForm K V) (x : V) : polar Q x x = 0 := by
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

variable [Finite K]

theorem exists_mul_self_eq (a : K) : ∃ s : K, s * s = a := by
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' a
  exact ⟨s, hs.symm⟩

variable {Q : QuadraticForm K V}

theorem exists_smul_eq_of_polar_eq_zero (hQ : Q.Anisotropic) {x y : V} (hx : x ≠ 0)
    (h : polar Q x y = 0) : ∃ c : K, c • x = y := by
  obtain ⟨s, hs⟩ := exists_mul_self_eq (Q y)
  obtain ⟨t, ht⟩ := exists_mul_self_eq (Q x)
  have h0 : s • x + t • y = 0 := hQ _ (by
    rw [apply_smul_add_smul, h, hs, ht, mul_zero, add_zero, mul_comm (Q y),
      CharTwo.add_self_eq_zero])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hx (hQ x (by rw [← ht, mul_zero]))
  refine ⟨-(t⁻¹ * s), ?_⟩
  rw [neg_smul, mul_smul, ← smul_neg, ← eq_neg_of_add_eq_zero_right h0, inv_smul_smul₀ ht0]

theorem polar_ne_zero (hQ : Q.Anisotropic) {x y : V} (hx : x ≠ 0) (hy : ∀ c : K, c • x ≠ y) :
    polar Q x y ≠ 0 := fun h => by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_polar_eq_zero hQ hx h
  exact hy c hc

theorem ker_polarBilin (hQ : Q.Anisotropic) {x : V} (hx : x ≠ 0) :
    LinearMap.ker (polarBilin Q x) = K ∙ x := by
  ext y
  rw [LinearMap.mem_ker, polarBilin_apply_apply, Submodule.mem_span_singleton]
  constructor
  · exact exists_smul_eq_of_polar_eq_zero hQ hx
  · rintro ⟨c, rfl⟩
    rw [polar_smul_right, polar_self_eq_zero, smul_zero]

theorem rank_le_two (hQ : Q.Anisotropic) : Module.rank K V ≤ 2 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [rank_subsingleton']
    exact zero_le
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  let φ : V →ₗ[K] V := (LinearMap.toSpanSingleton K V x).comp (polarBilin Q x)
  have hker : LinearMap.ker φ = K ∙ x := by
    rw [← ker_polarBilin hQ hx]
    ext y
    simp [φ, hx]
  have h1 : Module.rank K (LinearMap.range φ) ≤ 1 :=
    (rank_submodule_le_one_iff' _).2 ⟨x, by
      rintro _ ⟨y, rfl⟩
      exact Submodule.mem_span_singleton.2 ⟨polar Q x y, by simp [φ]⟩⟩
  have h2 : Module.rank K (LinearMap.ker φ) ≤ 1 :=
    (rank_submodule_le_one_iff' _).2 ⟨x, hker.le⟩
  rw [← LinearMap.rank_range_add_rank_ker φ]
  calc _ ≤ (1 : Cardinal) + 1 := add_le_add h1 h2
    _ = 2 := one_add_one_eq_two

theorem finiteDimensional (hQ : Q.Anisotropic) : FiniteDimensional K V :=
  Module.rank_lt_aleph0_iff.1 ((rank_le_two hQ).trans_lt Cardinal.ofNat_lt_aleph0)

theorem finrank_le_two (hQ : Q.Anisotropic) : finrank K V ≤ 2 :=
  Module.finrank_le_of_rank_le (by exact_mod_cast rank_le_two hQ)

theorem polar_div_smul_add_polar_div_smul (hQ : Q.Anisotropic) {x₀ w : V} (hx₀ : x₀ ≠ 0)
    (hw : ∀ c : K, c • x₀ ≠ w) (v : V) :
    (polar Q v w / polar Q x₀ w) • x₀ + (polar Q x₀ v / polar Q x₀ w) • w = v := by
  have hβ := polar_ne_zero hQ hx₀ hw
  set u := v - (polar Q v w / polar Q x₀ w) • x₀ - (polar Q x₀ v / polar Q x₀ w) • w with hu
  have hu1 : polar Q x₀ u = 0 := by
    rw [hu, polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right,
      polar_self_eq_zero, smul_zero, smul_eq_mul, div_mul_cancel₀ _ hβ]
    ring
  obtain ⟨c, hc⟩ := exists_smul_eq_of_polar_eq_zero hQ hx₀ hu1
  have hu2 : polar Q u w = 0 := by
    rw [hu, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left,
      polar_self_eq_zero, smul_zero, smul_eq_mul, div_mul_cancel₀ _ hβ]
    ring
  have hc0 : c = 0 := by
    rw [← hc, polar_smul_left, smul_eq_mul] at hu2
    exact (mul_eq_zero.1 hu2).resolve_right hβ
  rw [hc0, zero_smul, hu, sub_sub, eq_comm, sub_eq_zero] at hc
  exact hc.symm

end CharTwo

end CFSG.Timmesfeld.Transvection.QuadForm
