module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.Q8SqE9

open QuaternionGroup Subgroup

abbrev Q8 : Type := QuaternionGroup 2

@[expose] def kappa : Q8 × Q8 := (a 2, a 2)

structure Cfg {G : Type*} [Group G] (A B : Subgroup G) : Prop where
  comm : A ≤ centralizer (B : Set G)
  eA : Nonempty (A ≃* Q8)
  eB : Nonempty (B ≃* Q8)
  card : Nat.card ↥(A ⊔ B) = 32

theorem q8_central : ∀ u : Q8, (∀ w : Q8, u * w = w * u) → u = 1 ∨ u = a 2 := by decide +kernel

theorem q8_a2_sq : (a 2 : Q8) * a 2 = 1 := by decide +kernel

theorem q8_a2_ne_one : (a 2 : Q8) ≠ 1 := by decide +kernel

theorem q8_a2_central : ∀ w : Q8, (a 2 : Q8) * w = w * a 2 := by decide +kernel

theorem card_q8 : Nat.card Q8 = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

set_option synthInstance.maxSize 2000 in
theorem q8sq_pair : ∀ m₁ m₂ : Q8 × Q8, (m₁ ^ 2 ≠ 1 ∧ m₁ ^ 2 ≠ kappa) →
    (m₂ ^ 2 = m₁ ^ 2 ∨ m₂ ^ 2 = m₁ ^ 2 * kappa) →
    (m₂ * m₁ * m₂⁻¹ = m₁⁻¹ ∨ m₂ * m₁ * m₂⁻¹ = m₁⁻¹ * kappa) →
    ((m₁.2 = 1 ∨ m₁.2 = a 2) ∧ (m₂.2 = 1 ∨ m₂.2 = a 2)) ∨
      ((m₁.1 = 1 ∨ m₁.1 = a 2) ∧ (m₂.1 = 1 ∨ m₂.1 = a 2)) := by
  unfold kappa
  decide +kernel

variable {G : Type*} [Group G] {A B : Subgroup G}

namespace Cfg

theorem symm (h : Cfg A B) : Cfg B A where
  comm := Subgroup.le_centralizer_iff.mp h.comm
  eA := h.eB
  eB := h.eA
  card := by rw [sup_comm]; exact h.card

theorem card_A (h : Cfg A B) : Nat.card A = 8 := by
  rw [Nat.card_congr h.eA.some.toEquiv, card_q8]

theorem card_B (h : Cfg A B) : Nat.card B = 8 := h.symm.card_A

theorem ne (h : Cfg A B) : A ≠ B := by
  intro hAB
  have h1 := h.card
  rw [hAB, sup_idem, h.card_B] at h1
  omega

@[expose] noncomputable def phiA (h : Cfg A B) : Q8 →* G :=
  A.subtype.comp h.eA.some.symm.toMonoidHom

@[expose] noncomputable def phiB (h : Cfg A B) : Q8 →* G :=
  B.subtype.comp h.eB.some.symm.toMonoidHom

theorem phiA_inj (h : Cfg A B) : Function.Injective h.phiA :=
  Subtype.val_injective.comp h.eA.some.symm.injective

theorem phiB_inj (h : Cfg A B) : Function.Injective h.phiB :=
  Subtype.val_injective.comp h.eB.some.symm.injective

theorem phiA_mem (h : Cfg A B) (u : Q8) : h.phiA u ∈ A := (h.eA.some.symm u).2

theorem phiB_mem (h : Cfg A B) (u : Q8) : h.phiB u ∈ B := (h.eB.some.symm u).2

theorem exists_phiA (h : Cfg A B) {x : G} (hx : x ∈ A) : ∃ u, h.phiA u = x :=
  ⟨h.eA.some ⟨x, hx⟩, by simp [phiA]⟩

theorem exists_phiB (h : Cfg A B) {x : G} (hx : x ∈ B) : ∃ u, h.phiB u = x :=
  ⟨h.eB.some ⟨x, hx⟩, by simp [phiB]⟩

theorem commute_phi (h : Cfg A B) (u v : Q8) : Commute (h.phiA u) (h.phiB v) :=
  (Subgroup.mem_centralizer_iff.mp (h.comm (h.phiA_mem u)) _ (h.phiB_mem v)).symm

@[expose] noncomputable def pi (h : Cfg A B) : Q8 × Q8 →* G :=
  h.phiA.noncommCoprod h.phiB h.commute_phi

theorem pi_apply (h : Cfg A B) (m : Q8 × Q8) : h.pi m = h.phiA m.1 * h.phiB m.2 := rfl

theorem range_pi (h : Cfg A B) : h.pi.range = A ⊔ B := by
  have hA : h.phiA.range = A := by
    ext x
    exact ⟨fun ⟨u, hu⟩ => hu ▸ h.phiA_mem u, fun hx => h.exists_phiA hx⟩
  have hB : h.phiB.range = B := by
    ext x
    exact ⟨fun ⟨u, hu⟩ => hu ▸ h.phiB_mem u, fun hx => h.exists_phiB hx⟩
  rw [pi, MonoidHom.noncommCoprod_range, hA, hB]

theorem mem_sup_iff (h : Cfg A B) (x : G) : x ∈ A ⊔ B ↔ ∃ m, h.pi m = x := by
  rw [← h.range_pi]
  exact MonoidHom.mem_range

theorem pi_ker_sub (h : Cfg A B) {u v : Q8} (huv : h.pi (u, v) = 1) :
    (u = 1 ∨ u = a 2) ∧ (v = 1 ∨ v = a 2) := by
  rw [pi_apply] at huv
  simp only at huv
  refine ⟨q8_central u fun w => ?_, q8_central v fun w => ?_⟩
  · apply h.phiA_inj
    rw [map_mul, map_mul, eq_inv_of_mul_eq_one_left huv]
    exact ((h.commute_phi w v).inv_right).eq.symm
  · apply h.phiB_inj
    rw [map_mul, map_mul, eq_inv_of_mul_eq_one_right huv]
    exact ((h.commute_phi u w).inv_left).eq

theorem pi_not_injective (h : Cfg A B) : ¬ Function.Injective h.pi := by
  intro hinj
  have h1 : Nat.card h.pi.range = Nat.card (Q8 × Q8) :=
    Nat.card_congr (Equiv.ofInjective _ hinj).symm
  rw [range_pi, h.card, Nat.card_prod, card_q8] at h1
  omega

@[expose] noncomputable def z (h : Cfg A B) : G := h.phiA (a 2)

theorem z_mem_A (h : Cfg A B) : h.z ∈ A := h.phiA_mem _

theorem z_ne_one (h : Cfg A B) : h.z ≠ 1 := fun hz =>
  q8_a2_ne_one (h.phiA_inj (by rw [map_one]; exact hz))

theorem z_mul_self (h : Cfg A B) : h.z * h.z = 1 := by
  rw [z, ← map_mul, q8_a2_sq, map_one]

theorem pi_kappa (h : Cfg A B) : h.pi kappa = 1 := by
  by_contra hcon
  have hinj : Function.Injective h.pi := by
    rw [injective_iff_map_eq_one]
    intro m hm
    obtain ⟨u, v⟩ := m
    obtain ⟨h1, h2⟩ := h.pi_ker_sub hm
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · rfl
    · exfalso
      have : h.phiB (a 2) = 1 := by simpa [pi_apply] using hm
      exact q8_a2_ne_one (h.phiB_inj (by rw [this, map_one]))
    · exfalso
      have : h.phiA (a 2) = 1 := by simpa [pi_apply] using hm
      exact q8_a2_ne_one (h.phiA_inj (by rw [this, map_one]))
    · exact absurd hm hcon
  exact h.pi_not_injective hinj

theorem pi_eq_one_iff (h : Cfg A B) (m : Q8 × Q8) : h.pi m = 1 ↔ m = 1 ∨ m = kappa := by
  constructor
  · intro hm
    obtain ⟨u, v⟩ := m
    obtain ⟨h1, h2⟩ := h.pi_ker_sub hm
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have : h.phiB (a 2) = 1 := by simpa [pi_apply] using hm
      exact q8_a2_ne_one (h.phiB_inj (by rw [this, map_one]))
    · exfalso
      have : h.phiA (a 2) = 1 := by simpa [pi_apply] using hm
      exact q8_a2_ne_one (h.phiA_inj (by rw [this, map_one]))
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact map_one _
    · exact h.pi_kappa

theorem pi_eq_iff (h : Cfg A B) (m m' : Q8 × Q8) :
    h.pi m = h.pi m' ↔ m' = m ∨ m' = m * kappa := by
  have : h.pi m = h.pi m' ↔ h.pi (m⁻¹ * m') = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
  rw [this, pi_eq_one_iff, inv_mul_eq_one, inv_mul_eq_iff_eq_mul]
  exact or_congr eq_comm Iff.rfl

end Cfg

end CFSG.Quasithin.H13.Q8SqE9
