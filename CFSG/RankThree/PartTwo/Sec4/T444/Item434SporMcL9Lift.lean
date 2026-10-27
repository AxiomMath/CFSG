module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporMcL9

open scoped commutatorElement

variable {Y : Type*} [Group Y]

theorem comm_mul_central_left {z : Y} (hz : z ∈ Subgroup.center Y) (x y : Y) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have h1 : z * y = y * z := (Subgroup.mem_center_iff.mp hz y).symm
  simp only [commutatorElement_def]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [h1]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_mul_central_right {z : Y} (hz : z ∈ Subgroup.center Y) (x y : Y) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have h1 : z * x⁻¹ = x⁻¹ * z := (Subgroup.mem_center_iff.mp hz x⁻¹).symm
  simp only [commutatorElement_def]
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [h1]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_inv_right_of_central {x y : Y} (h : ⁅x, y⁆ ∈ Subgroup.center Y) :
    ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp h y⁻¹
  simp only [commutatorElement_def] at hc ⊢
  have e1 : y⁻¹ * (x * y * x⁻¹ * y⁻¹) * y = x * y * x⁻¹ * y⁻¹ := by
    calc y⁻¹ * (x * y * x⁻¹ * y⁻¹) * y = (x * y * x⁻¹ * y⁻¹) * y⁻¹ * y := by rw [hc]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  have e2 : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = (y⁻¹ * (x * y * x⁻¹ * y⁻¹) * y)⁻¹ := by group
  rw [e2, e1]

theorem comm_eq_one_of_conj_inv {Z : Subgroup Y} (hZ : Z ≤ Subgroup.center Y)
    (hZ3 : ∀ z ∈ Z, z ^ 3 = 1) {a b g ζ₁ ζ₂ : Y} (hab : ⁅a, b⁆ ∈ Z) (hζ₁ : ζ₁ ∈ Z)
    (hζ₂ : ζ₂ ∈ Z) (ha : g * a * g⁻¹ = a * ζ₁) (hb : g * b * g⁻¹ = b⁻¹ * ζ₂) : ⁅a, b⁆ = 1 := by
  have hcen : ⁅a, b⁆ ∈ Subgroup.center Y := hZ hab
  have h1 : g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
    rw [Subgroup.mem_center_iff.mp hcen g, mul_inv_cancel_right]
  have h2 : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [ha, hb, comm_mul_central_left (hZ hζ₁), comm_mul_central_right (hZ hζ₂),
    comm_inv_right_of_central hcen] at h2
  have h3 : ⁅a, b⁆ = ⁅a, b⁆⁻¹ := h1.symm.trans h2
  have h4 : ⁅a, b⁆ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [h3]
    exact inv_mul_cancel _
  have h5 : ⁅a, b⁆ ^ 3 = 1 := hZ3 _ hab
  calc ⁅a, b⁆ = ⁅a, b⁆ ^ 3 * (⁅a, b⁆ ^ 2)⁻¹ := by group
    _ = 1 := by rw [h4, h5]; simp

theorem cube_eq_one_of_conj_inv {Z : Subgroup Y} (hZ : Z ≤ Subgroup.center Y)
    (hZ3 : ∀ z ∈ Z, z ^ 3 = 1) {x g ζ : Y} (hx : x ^ 3 ∈ Z) (hζ : ζ ∈ Z)
    (hg : g * x * g⁻¹ = x⁻¹ * ζ) : x ^ 3 = 1 := by
  have h1 : g * x ^ 3 * g⁻¹ = x ^ 3 := by
    rw [Subgroup.mem_center_iff.mp (hZ hx) g, mul_inv_cancel_right]
  have h2 : g * x ^ 3 * g⁻¹ = (g * x * g⁻¹) ^ 3 := (conj_pow).symm
  have hcomm : Commute x⁻¹ ζ := Subgroup.mem_center_iff.mp (hZ hζ) x⁻¹
  rw [hg, hcomm.mul_pow, hZ3 ζ hζ, mul_one, inv_pow] at h2
  have h3 : x ^ 3 = (x ^ 3)⁻¹ := h1.symm.trans h2
  have h4 : (x ^ 3) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [h3]
    exact inv_mul_cancel _
  have h5 : (x ^ 3) ^ 3 = 1 := hZ3 _ hx
  calc x ^ 3 = (x ^ 3) ^ 3 * ((x ^ 3) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h4, h5]; simp

variable {H : Type*} [Group H]

theorem lift_commute_cube (ρ : Y →* H) (hker : ρ.ker ≤ Subgroup.center Y)
    (hZ3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) (x : Fin 4 → Y) (s t h : Y)
    (hcomm : ∀ a b, ρ (x a) * ρ (x b) = ρ (x b) * ρ (x a)) (hcube : ∀ a, ρ (x a) ^ 3 = 1)
    (hs0 : ρ s * ρ (x 0) * (ρ s)⁻¹ = ρ (x 0)) (hs1 : ρ s * ρ (x 1) * (ρ s)⁻¹ = ρ (x 1))
    (hs2 : ρ s * ρ (x 2) * (ρ s)⁻¹ = (ρ (x 2))⁻¹)
    (hs3 : ρ s * ρ (x 3) * (ρ s)⁻¹ = (ρ (x 3))⁻¹)
    (ht0 : ρ t * ρ (x 0) * (ρ t)⁻¹ = ρ (x 0))
    (ht1 : ρ t * ρ (x 1) * (ρ t)⁻¹ = (ρ (x 1))⁻¹)
    (ht2 : ρ t * ρ (x 2) * (ρ t)⁻¹ = ρ (x 2))
    (ht3 : ρ t * ρ (x 3) * (ρ t)⁻¹ = (ρ (x 3))⁻¹)
    (hh : ρ h * ρ (x 1) * (ρ h)⁻¹ = ρ (x 0) * ρ (x 2) ^ 2 * ρ (x 3) ^ 2) :
    (∀ a b, x a * x b = x b * x a) ∧ ∀ a, x a ^ 3 = 1 := by
  have hfix : ∀ {g a : Y}, ρ g * ρ a * (ρ g)⁻¹ = ρ a → ∃ ζ ∈ ρ.ker, g * a * g⁻¹ = a * ζ := by
    intro g a hg
    refine ⟨a⁻¹ * (g * a * g⁻¹), ?_, by group⟩
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [hg, inv_mul_cancel]
  have hinv : ∀ {g a : Y}, ρ g * ρ a * (ρ g)⁻¹ = (ρ a)⁻¹ →
      ∃ ζ ∈ ρ.ker, g * a * g⁻¹ = a⁻¹ * ζ := by
    intro g a hg
    refine ⟨a * (g * a * g⁻¹), ?_, by group⟩
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [hg, mul_inv_cancel]
  have hcm : ∀ a b, ⁅x a, x b⁆ ∈ ρ.ker := by
    intro a b
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm a b
  have hx3 : ∀ a, x a ^ 3 ∈ ρ.ker := fun a => by
    rw [MonoidHom.mem_ker, map_pow]
    exact hcube a
  have hpair : ∀ {a b : Fin 4} {g : Y}, (∃ ζ ∈ ρ.ker, g * x a * g⁻¹ = x a * ζ) →
      (∃ ζ ∈ ρ.ker, g * x b * g⁻¹ = (x b)⁻¹ * ζ) → x a * x b = x b * x a := by
    rintro a b g ⟨ζ₁, hζ₁, ha⟩ ⟨ζ₂, hζ₂, hb⟩
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (comm_eq_one_of_conj_inv hker hZ3 (hcm a b) hζ₁ hζ₂ ha hb)
  have h01 : x 0 * x 1 = x 1 * x 0 := hpair (hfix ht0) (hinv ht1)
  have h02 : x 0 * x 2 = x 2 * x 0 := hpair (hfix hs0) (hinv hs2)
  have h03 : x 0 * x 3 = x 3 * x 0 := hpair (hfix hs0) (hinv hs3)
  have h12 : x 1 * x 2 = x 2 * x 1 := hpair (hfix hs1) (hinv hs2)
  have h13 : x 1 * x 3 = x 3 * x 1 := hpair (hfix hs1) (hinv hs3)
  have h23 : x 2 * x 3 = x 3 * x 2 := hpair (hfix ht2) (hinv ht3)
  have hall : ∀ a b, x a * x b = x b * x a := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      first
        | rfl
        | exact h01
        | exact h01.symm
        | exact h02
        | exact h02.symm
        | exact h03
        | exact h03.symm
        | exact h12
        | exact h12.symm
        | exact h13
        | exact h13.symm
        | exact h23
        | exact h23.symm
  have hcub : ∀ {g : Y} {a : Fin 4}, (∃ ζ ∈ ρ.ker, g * x a * g⁻¹ = (x a)⁻¹ * ζ) → x a ^ 3 = 1 := by
    rintro g a ⟨ζ, hζ, hg⟩
    exact cube_eq_one_of_conj_inv hker hZ3 (hx3 a) hζ hg
  have c1 : x 1 ^ 3 = 1 := hcub (hinv ht1)
  have c2 : x 2 ^ 3 = 1 := hcub (hinv hs2)
  have c3 : x 3 ^ 3 = 1 := hcub (hinv hs3)
  have c0 : x 0 ^ 3 = 1 := by
    obtain ⟨ζ, hζ, hg⟩ : ∃ ζ ∈ ρ.ker, h * x 1 * h⁻¹ = x 0 * x 2 ^ 2 * x 3 ^ 2 * ζ := by
      refine ⟨(x 0 * x 2 ^ 2 * x 3 ^ 2)⁻¹ * (h * x 1 * h⁻¹), ?_, by group⟩
      simp only [MonoidHom.mem_ker, map_mul, map_inv, map_pow]
      rw [hh, inv_mul_cancel]
    have h1 : (h * x 1 * h⁻¹) ^ 3 = 1 := by
      have : (h * x 1 * h⁻¹) ^ 3 = h * x 1 ^ 3 * h⁻¹ := conj_pow
      rw [this, c1]
      group
    rw [hg] at h1
    have hzc : Commute (x 0 * x 2 ^ 2 * x 3 ^ 2) ζ := Subgroup.mem_center_iff.mp (hker hζ) _
    have hc02 : Commute (x 0) (x 2 ^ 2) := (show Commute (x 0) (x 2) from hall 0 2).pow_right 2
    have hc03 : Commute (x 0) (x 3 ^ 2) := (show Commute (x 0) (x 3) from hall 0 3).pow_right 2
    have hc23 : Commute (x 2 ^ 2) (x 3 ^ 2) :=
      ((show Commute (x 2) (x 3) from hall 2 3).pow_left 2).pow_right 2
    have hp2 : (x 2 ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, c2, one_pow]
    have hp3 : (x 3 ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, c3, one_pow]
    rw [hzc.mul_pow, hZ3 ζ hζ, mul_one, (hc03.mul_left hc23).mul_pow, hc02.mul_pow, hp2, hp3,
      mul_one, mul_one] at h1
    exact h1
  refine ⟨hall, fun a => ?_⟩
  fin_cases a <;> first | exact c0 | exact c1 | exact c2 | exact c3

end CFSG.RankThree.PartTwo.Sec4.Item434SporMcL9
