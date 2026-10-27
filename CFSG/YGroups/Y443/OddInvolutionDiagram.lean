module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.YGroups

namespace OddInvolutionDiagram

open scoped commutatorElement

section Diagram

variable {G : Type*} [Group G] {I : Type*}

theorem eq_of_pow_odd {A : Type*} [CommGroup A] {x y : A} (hx : x * x = 1) (hy : y * y = 1)
    {m : ℕ} (hm : Odd m) (h : (x * y) ^ m = 1) : x = y := by
  obtain ⟨r, rfl⟩ := hm
  have hx' : x ^ (2 * r + 1) = x := by
    rw [pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]
  have hy' : y ^ (2 * r + 1) = y := by
    rw [pow_succ, pow_mul, pow_two, hy, one_pow, one_mul]
  rw [mul_pow, hx', hy'] at h
  exact (eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hy)

theorem pair_mem_commutator (Γ : SimpleGraph I) (t : I → G) (hΓ : Γ.Connected)
    (hsq : ∀ i, t i * t i = 1)
    (hodd : ∀ i j, Γ.Adj i j → ∃ m : ℕ, Odd m ∧ (t i * t j) ^ m = 1) (i j : I) :
    t i * t j ∈ commutator G := by
  have hadj : ∀ i j, Γ.Adj i j → Abelianization.of (t i) = Abelianization.of (t j) := by
    intro i j hij
    obtain ⟨m, hm, hmij⟩ := hodd i j hij
    refine eq_of_pow_odd ?_ ?_ hm ?_
    · rw [← map_mul, hsq, map_one]
    · rw [← map_mul, hsq, map_one]
    · rw [← map_mul, ← map_pow, hmij, map_one]
  have hall : ∀ i j, Abelianization.of (t i) = Abelianization.of (t j) := by
    intro i j
    have h := (SimpleGraph.reachable_iff_reflTransGen i j).1 (hΓ.preconnected i j)
    induction h with
    | refl => rfl
    | tail _ hb ih => exact ih.trans (hadj _ _ hb)
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, hall i j, ← map_mul, hsq, map_one]

def edgeNormalClosure (Γ : SimpleGraph I) (t : I → G) : Subgroup G :=
  Subgroup.normalClosure {x | ∃ i j, Γ.Adj i j ∧ x = t i * t j}

theorem pair_mem_normalClosure (Γ : SimpleGraph I) (t : I → G) (hΓ : Γ.Connected)
    (hsq : ∀ i, t i * t i = 1) (i j : I) : t i * t j ∈ edgeNormalClosure Γ t := by
  have h := (SimpleGraph.reachable_iff_reflTransGen i j).1 (hΓ.preconnected i j)
  induction h with
  | refl => rw [hsq]; exact one_mem _
  | @tail b c _ hbc ih =>
    have : t i * t c = (t i * t b) * (t b * t c) := by
      rw [mul_assoc, ← mul_assoc (t b), hsq, one_mul]
    rw [this]
    exact mul_mem ih (Subgroup.subset_normalClosure ⟨b, c, hbc, rfl⟩)

theorem commutator_le_normalClosure (Γ : SimpleGraph I) (t : I → G) (hΓ : Γ.Connected)
    (hgen : Subgroup.closure (Set.range t) = ⊤) (hsq : ∀ i, t i * t i = 1) :
    commutator G ≤ edgeNormalClosure Γ t := by
  obtain ⟨i0⟩ := hΓ.nonempty
  let H := edgeNormalClosure Γ t
  have hnormal : H.Normal := Subgroup.normalClosure_normal
  let q := QuotientGroup.mk' H
  have hq : ∀ i, q (t i) = q (t i0) := by
    intro i
    have h1 : q (t i * t i0) = 1 := (QuotientGroup.eq_one_iff _).2
      (pair_mem_normalClosure Γ t hΓ hsq i i0)
    rw [map_mul] at h1
    have h2 : q (t i0) * q (t i0) = 1 := by rw [← map_mul, hsq, map_one]
    exact (eq_inv_of_mul_eq_one_left h1).trans (inv_eq_of_mul_eq_one_right h2)
  have hform : ∀ g : G, q g = 1 ∨ q g = q (t i0) := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range t) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Or.inr (hq i)
    | one => exact Or.inl (map_one q)
    | mul x y _ _ hx hy =>
      have h2 : q (t i0) * q (t i0) = 1 := by rw [← map_mul, hsq, map_one]
      rw [map_mul]
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
      · exact Or.inl (one_mul 1)
      · exact Or.inr (one_mul _)
      · exact Or.inr (mul_one _)
      · exact Or.inl h2
    | inv x _ hx =>
      have h2 : q (t i0) * q (t i0) = 1 := by rw [← map_mul, hsq, map_one]
      rw [map_inv]
      rcases hx with hx | hx <;> rw [hx]
      · exact Or.inl inv_one
      · exact Or.inr (inv_eq_of_mul_eq_one_right h2)
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro _ ⟨a, b, rfl⟩
  show ⁅a, b⁆ ∈ H
  rw [← QuotientGroup.ker_mk' H, MonoidHom.mem_ker, map_commutatorElement]
  rcases hform a with ha | ha <;> rcases hform b with hb | hb <;> rw [ha, hb] <;> simp

theorem conj_edge {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hca : c * a = a * c) (hcb : c * b = b * c) :
    (a * c)⁻¹ * (a * b) * (a * c) = (a * b)⁻¹ := by
  rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb,
    inv_eq_of_mul_eq_one_right hc]
  calc c * a * (a * b) * (a * c) = c * (a * a) * b * (a * c) := by simp only [mul_assoc]
    _ = c * b * (a * c) := by rw [ha, mul_one]
    _ = b * c * (a * c) := by rw [hcb]
    _ = b * (c * a) * c := by simp only [mul_assoc]
    _ = b * (a * c) * c := by rw [hca]
    _ = b * a * (c * c) := by simp only [mul_assoc]
    _ = b * a := by rw [hc, mul_one]

theorem edge_mem_commutator_commutator (Γ : SimpleGraph I) (t : I → G) (hΓ : Γ.Connected)
    (hsq : ∀ i, t i * t i = 1)
    (hodd : ∀ i j, Γ.Adj i j → ∃ m : ℕ, Odd m ∧ (t i * t j) ^ m = 1)
    (hcomm : ∀ i j, Γ.Adj i j → ∃ k, Commute (t k) (t i) ∧ Commute (t k) (t j)) {i j : I}
    (hij : Γ.Adj i j) : t i * t j ∈ ⁅commutator G, commutator G⁆ := by
  obtain ⟨m, hm, hmij⟩ := hodd i j hij
  obtain ⟨k, hki, hkj⟩ := hcomm i j hij
  have heN : t i * t j ∈ commutator G := pair_mem_commutator Γ t hΓ hsq hodd i j
  have hcN : t i * t k ∈ commutator G := pair_mem_commutator Γ t hΓ hsq hodd i k
  have key := conj_edge (hsq i) (hsq j) (hsq k) hki.eq hkj.eq
  have hcomm' : ⁅(t i * t k)⁻¹, t i * t j⁆ = (t i * t j)⁻¹ * (t i * t j)⁻¹ := by
    rw [commutatorElement_def, inv_inv, key]
  have h2 : (t i * t j)⁻¹ * (t i * t j)⁻¹ ∈ ⁅commutator G, commutator G⁆ := by
    rw [← hcomm']
    exact Subgroup.commutator_mem_commutator (inv_mem hcN) heN
  have h3 : (t i * t j) * (t i * t j) ∈ ⁅commutator G, commutator G⁆ := by
    have := inv_mem h2
    simpa [mul_inv_rev] using this
  obtain ⟨r, rfl⟩ := hm
  have h4 : ((t i * t j) * (t i * t j)) ^ r * (t i * t j) = 1 := by
    rw [← pow_two, ← pow_mul, ← pow_succ]
    exact hmij
  rw [eq_inv_of_mul_eq_one_right h4]
  exact inv_mem (pow_mem h3 r)

theorem commutator_commutator_eq (Γ : SimpleGraph I) (t : I → G) (hΓ : Γ.Connected)
    (hgen : Subgroup.closure (Set.range t) = ⊤) (hsq : ∀ i, t i * t i = 1)
    (hodd : ∀ i j, Γ.Adj i j → ∃ m : ℕ, Odd m ∧ (t i * t j) ^ m = 1)
    (hcomm : ∀ i j, Γ.Adj i j → ∃ k, Commute (t k) (t i) ∧ Commute (t k) (t j)) :
    ⁅commutator G, commutator G⁆ = commutator G := by
  have hH : edgeNormalClosure Γ t ≤ ⁅commutator G, commutator G⁆ := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨i, j, hij, rfl⟩
    exact edge_mem_commutator_commutator Γ t hΓ hsq hodd hcomm hij
  exact le_antisymm (Subgroup.commutator_le_self _)
    ((commutator_le_normalClosure Γ t hΓ hgen hsq).trans hH)

theorem isPerfect_commutator (Γ : SimpleGraph I) (t : I → G) (hΓ : Γ.Connected)
    (hgen : Subgroup.closure (Set.range t) = ⊤) (hsq : ∀ i, t i * t i = 1)
    (hodd : ∀ i j, Γ.Adj i j → ∃ m : ℕ, Odd m ∧ (t i * t j) ^ m = 1)
    (hcomm : ∀ i j, Γ.Adj i j → ∃ k, Commute (t k) (t i) ∧ Commute (t k) (t j)) :
    Group.IsPerfect (commutator G) :=
  Subgroup.isPerfect_iff.2 (commutator_commutator_eq Γ t hΓ hgen hsq hodd hcomm)

end Diagram

end OddInvolutionDiagram

end CFSG.YGroups
