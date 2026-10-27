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
public import Mathlib.GroupTheory.GroupAction.Primitive
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

namespace CFSG

namespace FiveTransitive.OrbitBounds

open MulAction

theorem isPretransitive_of_card_nine_of_large_group_of_small_fixedBy
    (K Y : Type) [Group K] [Fintype K] [Fintype Y] [MulAction K Y]
    (hYcard : Fintype.card Y = 9)
    (hfixed : ∀ k : K, k ≠ 1 → Nat.card (fixedBy Y k) ≤ 1)
    (hKcard : 8 < Fintype.card K) :
    IsPretransitive K Y := by
  classical
  letI : Nonempty Y := Fintype.card_pos_iff.mp (by omega)
  letI (k : K) : Fintype (fixedBy Y k) := Fintype.ofFinite _
  let Ω := orbitRel.Quotient K Y
  letI : Fintype Ω := Fintype.ofFinite Ω
  letI : Nonempty Ω :=
    ⟨⟦Classical.choice (inferInstance : Nonempty Y)⟧⟩
  have hburnside :=
    sum_card_fixedBy_eq_card_orbits_mul_card_group K Y
  have hone :
      Fintype.card (fixedBy Y (1 : K)) = 9 := by
    simp [hYcard]
  have hsum :
      (∑ k : K, Fintype.card (fixedBy Y k)) ≤
        Fintype.card K + 8 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : K)),
      hone]
    have herase :
        (∑ k ∈ Finset.univ.erase (1 : K),
          Fintype.card (fixedBy Y k)) ≤
            (Finset.univ.erase (1 : K)).card := by
      calc
        (∑ k ∈ Finset.univ.erase (1 : K),
            Fintype.card (fixedBy Y k)) ≤
            ∑ _k ∈ Finset.univ.erase (1 : K), 1 := by
              apply Finset.sum_le_sum
              intro k hk
              rw [← Nat.card_eq_fintype_card]
              exact hfixed k (Finset.ne_of_mem_erase hk)
        _ = (Finset.univ.erase (1 : K)).card := by simp
    rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : K)),
      Finset.card_univ] at herase
    omega
  have hΩcard : Fintype.card Ω = 1 := by
    have hΩpos : 0 < Fintype.card Ω := Fintype.card_pos
    by_contra hne
    have hΩtwo : 2 ≤ Fintype.card Ω := by omega
    have hproductLower :
        2 * Fintype.card K ≤ Fintype.card Ω * Fintype.card K :=
      Nat.mul_le_mul_right (Fintype.card K) hΩtwo
    rw [← hburnside] at hproductLower
    omega
  rw [pretransitive_iff_subsingleton_quotient K Y]
  exact Fintype.card_le_one_iff_subsingleton.mp (by
    change Fintype.card Ω ≤ 1
    omega)

theorem card_group_dvd_card_of_no_nontrivial_fixedPoints
    (K Y : Type) [Group K] [Fintype K] [Fintype Y] [MulAction K Y]
    (hfixed : ∀ k : K, k ≠ 1 → Nat.card (fixedBy Y k) = 0) :
    Fintype.card K ∣ Fintype.card Y := by
  classical
  letI (k : K) : Fintype (fixedBy Y k) := Fintype.ofFinite _
  let Ω := orbitRel.Quotient K Y
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hburnside :=
    sum_card_fixedBy_eq_card_orbits_mul_card_group K Y
  have hone :
      Fintype.card (fixedBy Y (1 : K)) = Fintype.card Y := by
    simp
  have herase :
      (∑ k ∈ Finset.univ.erase (1 : K),
        Fintype.card (fixedBy Y k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [← Nat.card_eq_fintype_card]
    exact hfixed k (Finset.ne_of_mem_erase hk)
  have hsum :
      (∑ k : K, Fintype.card (fixedBy Y k)) =
        Fintype.card Y := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : K)),
      hone, herase, zero_add]
  rw [hsum] at hburnside
  exact ⟨Fintype.card Ω, by
    simpa [Nat.mul_comm] using hburnside⟩

theorem normal_subgroup_card_eq_one_or_degree_dvd
    (H Y : Type) [Group H] [Fintype H] [Fintype Y]
    [MulAction H Y] [MulAction.IsPreprimitive H Y] [Nonempty Y]
    (hfaithful :
      ∀ h : H, (∀ y : Y, h • y = y) → h = 1)
    (N : Subgroup H) [N.Normal] :
    Nat.card N = 1 ∨ Nat.card Y ∣ Nat.card N := by
  classical
  by_cases hfixed : MulAction.fixedPoints N Y = Set.univ
  · left
    letI : Subsingleton N := ⟨fun a b => by
      apply Subtype.ext
      calc
        (a : H) = 1 := hfaithful a (fun y => by
          have hy : y ∈ MulAction.fixedPoints N Y := by
            rw [hfixed]
            exact Set.mem_univ y
          exact (MulAction.mem_fixedPoints.mp hy) a)
        _ = (b : H) := (hfaithful b (fun y => by
          have hy : y ∈ MulAction.fixedPoints N Y := by
            rw [hfixed]
            exact Set.mem_univ y
          exact (MulAction.mem_fixedPoints.mp hy) b)).symm⟩
    exact Nat.card_eq_one_iff_unique.mpr
      ⟨inferInstance, inferInstance⟩
  · right
    have htransitive : MulAction.IsPretransitive N Y :=
      MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed
    letI : MulAction.IsPretransitive N Y := htransitive
    let y : Y := Classical.choice inferInstance
    have hOrbitCard :
        Fintype.card (MulAction.orbit N y) = Fintype.card Y := by
      rw [MulAction.orbit_eq_univ N y]
      simp
    have hOrbitStabilizer :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group N y
    rw [hOrbitCard] at hOrbitStabilizer
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact ⟨Fintype.card (MulAction.stabilizer N y),
      hOrbitStabilizer.symm⟩

@[expose] def normalComapStabilizerEquivStabilizer
    (H Y : Type) [Group H] [MulAction H Y]
    (N : Subgroup H) (y : Y) :
    N.comap (MulAction.stabilizer H y).subtype ≃*
      MulAction.stabilizer N y where
  toFun a :=
    ⟨⟨((a.1 : MulAction.stabilizer H y) : H), a.prop⟩,
      a.1.prop⟩
  invFun b :=
    ⟨⟨((b.1 : N) : H), b.prop⟩, b.1.prop⟩
  left_inv a := by
    ext
    rfl
  right_inv b := by
    ext
    rfl
  map_mul' _ _ := rfl

end FiveTransitive.OrbitBounds

end CFSG
