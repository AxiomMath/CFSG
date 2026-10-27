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

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

public theorem mem_closure_triple_form {G : Type*} [Group G] (r x c : G)
    (hcr : c * r = r * c) (hcx : c * x = x * c)
    (hrx : r * x * r⁻¹ ∈ Subgroup.zpowers x) (hrx' : r⁻¹ * x * r ∈ Subgroup.zpowers x)
    {m : G} (hm : m ∈ Subgroup.closure ({r, x, c} : Set G)) :
    ∃ j i l : ℤ, m = r ^ j * x ^ i * c ^ l := by
  have hcr' : Commute c r := hcr
  have hcx' : Commute c x := hcx
  have conjK : ∀ a : G, a * x * a⁻¹ ∈ Subgroup.zpowers x →
      ∀ h ∈ Subgroup.zpowers x, a * h * a⁻¹ ∈ Subgroup.zpowers x := by
    intro a ha h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ ha k
  have hrinv : r⁻¹ * x * r⁻¹⁻¹ ∈ Subgroup.zpowers x := by
    rw [inv_inv]
    exact hrx'
  have hrN : r ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact conjK r hrx h hh
    · intro hh
      have h2 := conjK r⁻¹ hrinv (r * h * r⁻¹) hh
      have e : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ = h := by group
      rwa [e] at h2
  have K1 : ∀ n : ℤ, ∀ h ∈ Subgroup.zpowers x,
      r ^ n * h * (r ^ n)⁻¹ ∈ Subgroup.zpowers x := by
    intro n h hh
    exact (Subgroup.mem_set_normalizer_iff.mp (Subgroup.zpow_mem _ hrN n) h).mp hh
  have F3 : ∀ j i : ℤ, ∃ k : ℤ, x ^ i * r ^ j = r ^ j * x ^ k := by
    intro j i
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (K1 (-j) (x ^ i) (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) i))
    refine ⟨k, ?_⟩
    rw [hk]
    group
  induction hm using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨j, i, l, rfl⟩ := iha
    obtain ⟨j', i', l', rfl⟩ := ihb
    obtain ⟨k, hk⟩ := F3 j' i
    have hcomm : Commute (c ^ l) (r ^ j' * x ^ i') :=
      ((hcr'.zpow_right j').mul_right (hcx'.zpow_right i')).zpow_left l
    refine ⟨j + j', k + i', l + l', ?_⟩
    calc r ^ j * x ^ i * c ^ l * (r ^ j' * x ^ i' * c ^ l')
        = r ^ j * x ^ i * (c ^ l * (r ^ j' * x ^ i')) * c ^ l' := by group
      _ = r ^ j * x ^ i * (r ^ j' * x ^ i' * c ^ l) * c ^ l' := by rw [hcomm.eq]
      _ = r ^ j * (x ^ i * r ^ j') * x ^ i' * (c ^ l * c ^ l') := by group
      _ = r ^ j * (r ^ j' * x ^ k) * x ^ i' * (c ^ l * c ^ l') := by rw [hk]
      _ = r ^ (j + j') * x ^ (k + i') * c ^ (l + l') := by group
  | inv a _ iha =>
    obtain ⟨j, i, l, rfl⟩ := iha
    obtain ⟨k, hk⟩ := F3 (-j) (-i)
    have hcomm : Commute (c ^ (-l)) (r ^ (-j) * x ^ k) :=
      ((hcr'.zpow_right (-j)).mul_right (hcx'.zpow_right k)).zpow_left (-l)
    refine ⟨-j, k, -l, ?_⟩
    calc (r ^ j * x ^ i * c ^ l)⁻¹ = c ^ (-l) * (x ^ (-i) * r ^ (-j)) := by group
      _ = c ^ (-l) * (r ^ (-j) * x ^ k) := by rw [hk]
      _ = (r ^ (-j) * x ^ k) * c ^ (-l) := hcomm.eq
      _ = r ^ (-j) * x ^ k * c ^ (-l) := by group

public theorem zpow_conj_of_comm {G : Type*} [Group G] (x a d : G) (m : ℤ)
    (h : x * a * x⁻¹ = d ^ m * a) (hxd : x * d = d * x) (had : a * d = d * a) (i : ℤ) :
    x ^ i * a * (x ^ i)⁻¹ = d ^ (i * m) * a := by
  have hxdc : Commute x d := hxd
  have hfix : ∀ k : ℤ, x * d ^ k * x⁻¹ = d ^ k := fun k => by
    rw [(hxdc.zpow_right k).eq, mul_inv_cancel_right]
  have hfix' : ∀ k : ℤ, x⁻¹ * d ^ k * x = d ^ k := fun k => by
    rw [mul_assoc, ← (hxdc.zpow_right k).eq, inv_mul_cancel_left]
  have h2 : x⁻¹ * a * x = d ^ (-m) * a := by
    have e1 : a = d ^ m * (x⁻¹ * a * x) := by
      calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
        _ = x⁻¹ * (d ^ m * a) * x := by rw [h]
        _ = (x⁻¹ * d ^ m * x) * (x⁻¹ * a * x) := by group
        _ = d ^ m * (x⁻¹ * a * x) := by rw [hfix' m]
    calc x⁻¹ * a * x = d ^ (-m) * (d ^ m * (x⁻¹ * a * x)) := by group
      _ = d ^ (-m) * a := by rw [← e1]
  induction i using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have hx1 : x ^ ((k : ℤ) + 1) = x * x ^ (k : ℤ) := by
      rw [add_comm, zpow_add, zpow_one]
    rw [hx1]
    calc x * x ^ (k : ℤ) * a * (x * x ^ (k : ℤ))⁻¹
        = x * (x ^ (k : ℤ) * a * (x ^ (k : ℤ))⁻¹) * x⁻¹ := by group
      _ = x * (d ^ ((k : ℤ) * m) * a) * x⁻¹ := by rw [ih]
      _ = (x * d ^ ((k : ℤ) * m) * x⁻¹) * (x * a * x⁻¹) := by group
      _ = d ^ ((k : ℤ) * m) * (d ^ m * a) := by rw [hfix, h]
      _ = d ^ (((k : ℤ) + 1) * m) * a := by
        rw [add_mul, one_mul, zpow_add]
        group
  | pred k ih =>
    have hx1 : x ^ (-(k : ℤ) - 1) = x⁻¹ * x ^ (-(k : ℤ)) := by
      rw [show -(k : ℤ) - 1 = -1 + -(k : ℤ) by ring, zpow_add, zpow_neg_one]
    rw [hx1]
    calc x⁻¹ * x ^ (-(k : ℤ)) * a * (x⁻¹ * x ^ (-(k : ℤ)))⁻¹
        = x⁻¹ * (x ^ (-(k : ℤ)) * a * (x ^ (-(k : ℤ)))⁻¹) * x := by group
      _ = x⁻¹ * (d ^ (-(k : ℤ) * m) * a) * x := by rw [ih]
      _ = (x⁻¹ * d ^ (-(k : ℤ) * m) * x) * (x⁻¹ * a * x) := by group
      _ = d ^ (-(k : ℤ) * m) * (d ^ (-m) * a) := by rw [hfix', h2]
      _ = d ^ ((-(k : ℤ) - 1) * m) * a := by
        rw [show (-(k : ℤ) - 1) * m = -(k : ℤ) * m + -m by ring, zpow_add]
        group

public theorem mem_sup_zpowers_form {G : Type*} [Group G] (R : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (R : Set G)) {z : G} (hz : z ∈ R ⊔ Subgroup.zpowers g) :
    ∃ u ∈ R, ∃ j : ℤ, z = u * g ^ j := by
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr hg
  have heq := Subgroup.coe_mul_of_right_le_normalizer_left R (Subgroup.zpowers g) hle
  have hz' : z ∈ ((R ⊔ Subgroup.zpowers g : Subgroup G) : Set G) := hz
  rw [heq] at hz'
  obtain ⟨u, hu, y, hy, huy⟩ := Set.mem_mul.mp hz'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨u, hu, j, huy.symm⟩

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
