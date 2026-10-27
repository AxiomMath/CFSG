module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin

namespace X1512

variable {K : Type*} [Group K]

abbrev CosetOf (C : Subgroup K) (x : K) : Type _ := {y : K // x⁻¹ * y ∈ C}

theorem conj_mem_coset {C : Subgroup K} [C.Normal] {x a y : K} (hx : a * x * a⁻¹ * x⁻¹ ∈ C)
    (hy : x⁻¹ * y ∈ C) : x⁻¹ * (a * y * a⁻¹) ∈ C := by
  have h1 : x⁻¹ * a * x * a⁻¹ ∈ C := by
    have := Subgroup.Normal.conj_mem inferInstance _ hx x⁻¹
    simpa [mul_assoc] using this
  have h2 : a * (x⁻¹ * y) * a⁻¹ ∈ C := Subgroup.Normal.conj_mem inferInstance _ hy a
  have e : x⁻¹ * (a * y * a⁻¹) = (x⁻¹ * a * x * a⁻¹) * (a * (x⁻¹ * y) * a⁻¹) := by group
  rw [e]
  exact C.mul_mem h1 h2

@[instance_reducible] noncomputable def cosetAction (C A₀ : Subgroup K) [C.Normal] {x : K}
    (hx : ∀ a ∈ A₀, a * x * a⁻¹ * x⁻¹ ∈ C) : MulAction ↥A₀ (CosetOf C x) where
  smul a y := ⟨a * y.1 * (a : K)⁻¹, conj_mem_coset (hx a a.2) y.2⟩
  one_smul y := Subtype.ext (by
    show (1 : ↥A₀).1 * y.1 * ((1 : ↥A₀).1)⁻¹ = y.1
    simp)
  mul_smul a b y := Subtype.ext (by
    show (a * b : ↥A₀).1 * y.1 * ((a * b : ↥A₀).1)⁻¹ = a.1 * (b.1 * y.1 * b.1⁻¹) * a.1⁻¹
    simp [mul_assoc])

theorem exists_fixed_mem_coset [Finite K] {C A₀ : Subgroup K} [C.Normal] (hC : Odd (Nat.card C))
    (hA : IsPGroup 2 A₀) {x : K} (hx : ∀ a ∈ A₀, a * x * a⁻¹ * x⁻¹ ∈ C) :
    ∃ y : K, x⁻¹ * y ∈ C ∧ ∀ a ∈ A₀, a * y * a⁻¹ = y := by
  let _ : MulAction ↥A₀ (CosetOf C x) := cosetAction C A₀ hx
  have : Finite (CosetOf C x) := Subtype.finite
  have hcard : Nat.card (CosetOf C x) = Nat.card C :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft x⁻¹) fun _ => Iff.rfl)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hA.card_modEq_card_fixedPoints (α := CosetOf C x)
  have hodd : Odd (Nat.card (MulAction.fixedPoints ↥A₀ (CosetOf C x))) := by
    have h2 : Nat.card (CosetOf C x) % 2 = Nat.card (MulAction.fixedPoints ↥A₀ (CosetOf C x)) % 2 :=
      hmod
    rw [hcard] at h2
    rw [Nat.odd_iff] at hC ⊢
    omega
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥A₀ (CosetOf C x)) := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have : Finite (MulAction.fixedPoints ↥A₀ (CosetOf C x)) := Subtype.finite
  obtain ⟨⟨y, hy⟩⟩ := Nat.card_pos_iff.mp hpos |>.1
  refine ⟨y.1, y.2, fun a ha => ?_⟩
  have := hy ⟨a, ha⟩
  exact congrArg Subtype.val this

theorem exists_lift_inverted {a₁ y₀ : K} (ha₁ : a₁ * a₁ = 1) :
    a₁ * (y₀⁻¹ * (a₁ * y₀ * a₁⁻¹)) * a₁⁻¹ = (y₀⁻¹ * (a₁ * y₀ * a₁⁻¹))⁻¹ := by
  have h : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right ha₁
  have e1 : a₁ * (y₀⁻¹ * (a₁ * y₀ * a₁⁻¹)) * a₁⁻¹ = (a₁ * y₀⁻¹ * a₁ * y₀) * (a₁⁻¹ * a₁⁻¹) := by
    group
  have e2 : (y₀⁻¹ * (a₁ * y₀ * a₁⁻¹))⁻¹ = a₁ * y₀⁻¹ * a₁⁻¹ * y₀ := by group
  rw [e1, e2, h, ha₁, mul_one]

end X1512

end CFSG.Quasithin
