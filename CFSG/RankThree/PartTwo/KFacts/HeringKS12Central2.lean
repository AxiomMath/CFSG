module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.RankThree.PartTwo.KFacts

private theorem eq_one_of_mul_central_of_cube {C : Type*} [Group C] {u v z : C}
    (hz : z ∈ Subgroup.center C) (hz2 : z ^ 2 = 1) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (h : u = z * v) : z = 1 := by
  have hc : Commute z v := (Subgroup.mem_center_iff.mp hz v).symm
  have h3 : (z * v) ^ 3 = 1 := by rw [← h]; exact hu
  rw [hc.mul_pow 3, hv, mul_one] at h3
  have hz3 : z ^ 3 = z := by rw [pow_succ, hz2, one_mul]
  rw [hz3] at h3
  exact h3

theorem exists_config_of_quotient_two {C : Type*} [Group C] (N : Subgroup C) [N.Normal]
    (hNc : N ≤ Subgroup.center C) (hN2 : ∀ z ∈ N, z ^ 2 = 1) {x₀ y₀ g₀ h₀ : C ⧸ N}
    (hx3 : x₀ ^ 3 = 1) (hy3 : y₀ ^ 3 = 1) (hxy : x₀ * y₀ = y₀ * x₀)
    (hgx : g₀ * x₀ * g₀⁻¹ = x₀⁻¹) (hgy : g₀ * y₀ * g₀⁻¹ = y₀) (hhx : h₀ * x₀ * h₀⁻¹ = x₀)
    (hhy : h₀ * y₀ * h₀⁻¹ = y₀⁻¹)
    (hdist : ∀ i j k l : Fin 3, x₀ ^ (i : ℕ) * y₀ ^ (j : ℕ) = x₀ ^ (k : ℕ) * y₀ ^ (l : ℕ) →
      i = k ∧ j = l) :
    ∃ x y g h : C, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ g * x * g⁻¹ = x⁻¹ ∧
      g * y * g⁻¹ = y ∧ h * x * h⁻¹ = x ∧ h * y * h⁻¹ = y⁻¹ ∧
      ∀ i j k l : Fin 3, x ^ (i : ℕ) * y ^ (j : ℕ) = x ^ (k : ℕ) * y ^ (l : ℕ) → i = k ∧ j = l := by
  obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective x₀
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective y₀
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective g₀
  obtain ⟨h₁, rfl⟩ := QuotientGroup.mk_surjective h₀
  have key : ∀ a : C, (a : C ⧸ N) = 1 → a ∈ N := fun a ha =>
    (QuotientGroup.eq_one_iff a).mp ha
  have hx3N : x₁ ^ 3 ∈ N := key _ (by rw [QuotientGroup.mk_pow]; exact hx3)
  have hy3N : y₁ ^ 3 ∈ N := key _ (by rw [QuotientGroup.mk_pow]; exact hy3)
  have hcube4 : ∀ w : C, w ^ 3 ∈ N → (w ^ 4) ^ 3 = 1 := by
    intro w hw
    rw [pow_right_comm, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hN2 _ hw, one_pow]
  have hx4 : ((x₁ ^ 4 : C) : C ⧸ N) = (x₁ : C ⧸ N) := by
    rw [QuotientGroup.mk_pow, show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hx3, one_mul]
  have hy4 : ((y₁ ^ 4 : C) : C ⧸ N) = (y₁ : C ⧸ N) := by
    rw [QuotientGroup.mk_pow, show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hy3, one_mul]
  obtain ⟨x, hxq, hx3'⟩ : ∃ x : C, (x : C ⧸ N) = (x₁ : C ⧸ N) ∧ x ^ 3 = 1 :=
    ⟨x₁ ^ 4, hx4, hcube4 x₁ hx3N⟩
  obtain ⟨y, hyq, hy3'⟩ : ∃ y : C, (y : C ⧸ N) = (y₁ : C ⧸ N) ∧ y ^ 3 = 1 :=
    ⟨y₁ ^ 4, hy4, hcube4 y₁ hy3N⟩
  refine ⟨x, y, g₁, h₁, hx3', hy3', ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hzN : x * y * x⁻¹ * y⁻¹ ∈ N := key _ (by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxq, hyq]
      rw [hxy, mul_inv_cancel_right, mul_inv_cancel])
    have hu : (x * y * x⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3', mul_one, mul_inv_cancel]
    have hz := eq_one_of_mul_central_of_cube (u := x * y * x⁻¹) (v := y) (hNc hzN)
      (hN2 _ hzN) hu hy3' (inv_mul_cancel_right _ _).symm
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hz)
  ·
    have hzN : g₁ * x * g₁⁻¹ * x ∈ N := key _ (by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxq]
      rw [hgx, inv_mul_cancel])
    have hu : (g₁ * x * g₁⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3', mul_one, mul_inv_cancel]
    have hv : (x⁻¹) ^ 3 = 1 := by rw [inv_pow, hx3', inv_one]
    have hz := eq_one_of_mul_central_of_cube (u := g₁ * x * g₁⁻¹) (v := x⁻¹) (hNc hzN)
      (hN2 _ hzN) hu hv (mul_inv_cancel_right _ _).symm
    exact mul_eq_one_iff_eq_inv.mp hz
  ·
    have hzN : g₁ * y * g₁⁻¹ * y⁻¹ ∈ N := key _ (by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hyq]
      rw [hgy, mul_inv_cancel])
    have hu : (g₁ * y * g₁⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3', mul_one, mul_inv_cancel]
    have hz := eq_one_of_mul_central_of_cube (u := g₁ * y * g₁⁻¹) (v := y) (hNc hzN)
      (hN2 _ hzN) hu hy3' (inv_mul_cancel_right _ _).symm
    exact mul_inv_eq_one.mp hz
  ·
    have hzN : h₁ * x * h₁⁻¹ * x⁻¹ ∈ N := key _ (by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxq]
      rw [hhx, mul_inv_cancel])
    have hu : (h₁ * x * h₁⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3', mul_one, mul_inv_cancel]
    have hz := eq_one_of_mul_central_of_cube (u := h₁ * x * h₁⁻¹) (v := x) (hNc hzN)
      (hN2 _ hzN) hu hx3' (inv_mul_cancel_right _ _).symm
    exact mul_inv_eq_one.mp hz
  ·
    have hzN : h₁ * y * h₁⁻¹ * y ∈ N := key _ (by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hyq]
      rw [hhy, inv_mul_cancel])
    have hu : (h₁ * y * h₁⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3', mul_one, mul_inv_cancel]
    have hv : (y⁻¹) ^ 3 = 1 := by rw [inv_pow, hy3', inv_one]
    have hz := eq_one_of_mul_central_of_cube (u := h₁ * y * h₁⁻¹) (v := y⁻¹) (hNc hzN)
      (hN2 _ hzN) hu hv (mul_inv_cancel_right _ _).symm
    exact mul_eq_one_iff_eq_inv.mp hz
  ·
    intro i j k l hijkl
    apply hdist i j k l
    have h' := congrArg (fun w : C => (w : C ⧸ N)) hijkl
    simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, hxq, hyq] using h'

end CFSG.RankThree.PartTwo.KFacts
