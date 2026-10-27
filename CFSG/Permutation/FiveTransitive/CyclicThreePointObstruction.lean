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

namespace CFSG

namespace FiveTransitive.CyclicThreePointObstruction

theorem false_of_cyclic_factor_range_card_six
    (N A F : Type) [Group N] [Group A] [Fintype F]
    [IsCyclic A]
    (η : N →* A) (hη : Function.Surjective η)
    (ρ : N →* Equiv.Perm F)
    (hker : η.ker ≤ ρ.ker)
    (hFcard : Fintype.card F = 3)
    (hrangeCard : Nat.card ρ.range = 6) :
    False := by
  classical
  let ρ' : N →* ρ.range := ρ.rangeRestrict
  have hker' : η.ker ≤ ρ'.ker := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn ⊢
    apply Subtype.ext
    change ρ n = 1
    exact MonoidHom.mem_ker.mp (hker hn)
  let θ : A →* ρ.range :=
    η.liftOfSurjective hη ⟨ρ', hker'⟩
  have hθcomp : θ.comp η = ρ' := by
    simp [θ]
  have hθsurjective : Function.Surjective θ := by
    intro q
    obtain ⟨n, hn⟩ := q.prop
    refine ⟨η n, ?_⟩
    apply Subtype.ext
    change (θ.comp η n : Equiv.Perm F) = q
    rw [hθcomp]
    exact hn
  letI : IsCyclic ρ.range :=
    isCyclic_of_surjective θ hθsurjective
  letI : IsMulCommutative ρ.range :=
    IsCyclic.isMulCommutative
  have hpermCard :
      Nat.card (Equiv.Perm F) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      hFcard]
    norm_num
  have hrangeTop :
      ρ.range = (⊤ : Subgroup (Equiv.Perm F)) := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hpermCard, hrangeCard]
  have hcomm : IsMulCommutative (Equiv.Perm F) := by
    constructor
    constructor
    intro a b
    have ha : a ∈ ρ.range := by
      rw [hrangeTop]
      exact Subgroup.mem_top a
    have hb : b ∈ ρ.range := by
      rw [hrangeTop]
      exact Subgroup.mem_top b
    exact congrArg Subtype.val
      (mul_comm' (⟨a, ha⟩ : ρ.range)
        (⟨b, hb⟩ : ρ.range))
  have hcardLe :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mp hcomm
  rw [Nat.card_eq_fintype_card, hFcard] at hcardLe
  omega

end FiveTransitive.CyclicThreePointObstruction

end CFSG
