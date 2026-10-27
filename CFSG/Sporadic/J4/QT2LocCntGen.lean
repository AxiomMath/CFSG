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

namespace CFSG.Sporadic.J4.QT2

theorem incidence_le {P X : Type*} (Δ : Finset P) (Z : Finset X) (R : P → X → Prop)
    [∀ p x, Decidable (R p x)] (m : ℕ) (hm : ∀ p ∈ Δ, (Z.filter (R p)).card ≤ m) (z : X)
    (hY : ∀ x ∈ Z, (Δ.filter (fun p => R p z)).card ≤ (Δ.filter (fun p => R p x)).card) :
    Z.card * (Δ.filter (fun p => R p z)).card ≤ Δ.card * m := by
  have h1 : Z.card • (Δ.filter (fun p => R p z)).card ≤
      ∑ x ∈ Z, (Δ.filter (fun p => R p x)).card := Finset.card_nsmul_le_sum _ _ _ hY
  have h2 : ∑ x ∈ Z, (Δ.filter (fun p => R p x)).card =
      ∑ p ∈ Δ, (Z.filter (R p)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h3 : ∑ p ∈ Δ, (Z.filter (R p)).card ≤ Δ.card * m := by
    calc ∑ p ∈ Δ, (Z.filter (R p)).card ≤ ∑ _p ∈ Δ, m := Finset.sum_le_sum hm
      _ = Δ.card * m := by simp
  rw [smul_eq_mul] at h1
  omega

theorem incidence_le_ncard {P X : Type*} [Finite P] [Finite X] (Δ : Set P) (Z : Set X)
    (R : P → X → Prop) (m : ℕ) (hm : ∀ p ∈ Δ, {x | x ∈ Z ∧ R p x}.ncard ≤ m) (z : X)
    (hY : ∀ x ∈ Z, {p | p ∈ Δ ∧ R p z}.ncard ≤ {p | p ∈ Δ ∧ R p x}.ncard) :
    Z.ncard * {p | p ∈ Δ ∧ R p z}.ncard ≤ Δ.ncard * m := by
  classical
  have hΔ := Set.toFinite Δ
  have hZ := Set.toFinite Z
  have key := incidence_le hΔ.toFinset hZ.toFinset R m (fun p hp => ?_) z (fun x hx => ?_)
  · have e1 : ∀ x : X, (hΔ.toFinset.filter (fun p => R p x)).card = {p | p ∈ Δ ∧ R p x}.ncard := by
      intro x
      rw [← Set.ncard_coe_finset]
      congr 1
      ext p
      simp
    rw [e1 z, ← Set.ncard_eq_toFinset_card Z hZ, ← Set.ncard_eq_toFinset_card Δ hΔ] at key
    exact key
  · have e : (hZ.toFinset.filter (R p)).card = {x | x ∈ Z ∧ R p x}.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext x
      simp
    rw [e]
    exact hm p (hΔ.mem_toFinset.1 hp)
  · have e1 : ∀ y : X, (hΔ.toFinset.filter (fun p => R p y)).card = {p | p ∈ Δ ∧ R p y}.ncard := by
      intro y
      rw [← Set.ncard_coe_finset]
      congr 1
      ext p
      simp
    rw [e1, e1]
    exact hY x (hZ.mem_toFinset.1 hx)

theorem orbit_subset_of {G X : Type*} [Group G] [MulAction G X] (K : Subgroup G) (b : X)
    (S : Set X) (hS : ∀ q ∈ K, q • b ∈ S) : MulAction.orbit K b ⊆ S := by
  rintro v ⟨q, rfl⟩
  exact hS q q.2

theorem nat_card_orbit_mul {G X : Type*} [Group G] [MulAction G X] (b : X) :
    Nat.card (MulAction.orbit G b) * Nat.card (MulAction.stabilizer G b) = Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G b)

theorem card_eq_orbit_mul_inf {G X : Type*} [Group G] [MulAction G X] (K H : Subgroup G) (b : X)
    (hH : ∀ g : G, g • b = b ↔ g ∈ H) :
    Nat.card ↥K = Nat.card (MulAction.orbit K b) * Nat.card ↥(K ⊓ H) := by
  rw [← nat_card_orbit_mul (G := K) b]
  congr 1
  apply Nat.card_congr
  exact
    { toFun := fun q => ⟨(q.1 : G), q.1.2, (hH _).1 (MulAction.mem_stabilizer_iff.1 q.2)⟩
      invFun := fun x => ⟨⟨(x : G), x.2.1⟩, MulAction.mem_stabilizer_iff.2 ((hH _).2 x.2.2)⟩
      left_inv := fun q => rfl
      right_inv := fun x => rfl }

theorem card_eq_card_mul_centralizer {G : Type*} [Group G] (H : Subgroup G) (z : G) (Z : Finset G)
    (hz : z ∈ Z) (hconj : ∀ h ∈ H, ∀ x ∈ Z, h * x * h⁻¹ ∈ Z)
    (htrans : ∀ x ∈ Z, ∃ h ∈ H, h * z * h⁻¹ = x) :
    Nat.card ↥H = Z.card * Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ H) := by
  let _ : MulAction ↥H G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp H.subtype)
  have hsmul : ∀ (h : ↥H) (x : G), h • x = (h : G) * x * (h : G)⁻¹ := fun h x => rfl
  rw [← nat_card_orbit_mul (G := ↥H) z]
  have horb : MulAction.orbit ↥H z = ↑Z := by
    ext x
    rw [MulAction.mem_orbit_iff, Finset.mem_coe]
    constructor
    · rintro ⟨h, rfl⟩
      rw [hsmul]
      exact hconj h h.2 z hz
    · intro hx
      obtain ⟨h, hh, e⟩ := htrans x hx
      exact ⟨⟨h, hh⟩, by rw [hsmul]; exact e⟩
  have hcard : Nat.card ↥(MulAction.orbit ↥H z) = Z.card := by
    rw [horb, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcard]
  congr 1
  apply Nat.card_congr
  exact
    { toFun := fun h => ⟨(h.1 : G), by
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have := MulAction.mem_stabilizer_iff.1 h.2
        rw [hsmul] at this
        calc (h.1 : G) * z = ((h.1 : G) * z * (h.1 : G)⁻¹) * (h.1 : G) := by group
          _ = z * (h.1 : G) := by rw [this], h.1.2⟩
      invFun := fun x => ⟨⟨(x : G), x.2.2⟩, MulAction.mem_stabilizer_iff.2 (by
        rw [hsmul]
        have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2.1
        calc (x : G) * z * (x : G)⁻¹ = (z * (x : G)) * (x : G)⁻¹ := by rw [hx]
          _ = z := by group)⟩
      left_inv := fun h => rfl
      right_inv := fun x => rfl }

theorem card_centralizer_singleton_conj {G : Type*} [Group G] (h x : G) :
    Nat.card ↥(Subgroup.centralizer ({h * x * h⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
  apply Nat.card_congr
  exact
    { toFun := fun q => ⟨h⁻¹ * q * h, by
        have hq := Subgroup.mem_centralizer_singleton_iff.1 q.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc h⁻¹ * (q : G) * h * x = h⁻¹ * ((q : G) * (h * x * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * x * h⁻¹) * (q : G)) * h := by rw [hq]
          _ = x * (h⁻¹ * (q : G) * h) := by group⟩
      invFun := fun q => ⟨h * q * h⁻¹, by
        have hq := Subgroup.mem_centralizer_singleton_iff.1 q.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc h * (q : G) * h⁻¹ * (h * x * h⁻¹) = h * ((q : G) * x) * h⁻¹ := by group
          _ = h * (x * (q : G)) * h⁻¹ := by rw [hq]
          _ = (h * x * h⁻¹) * (h * (q : G) * h⁻¹) := by group⟩
      left_inv := fun q => Subtype.ext (by simp [mul_assoc])
      right_inv := fun q => Subtype.ext (by simp [mul_assoc]) }

end CFSG.Sporadic.J4.QT2
