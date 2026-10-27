module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_14
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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.SignalizerFunctorTheorem.McBride.Thompson

theorem fpf_nilpotent {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime)
    {Z : Subgroup Γ} {a : Γ} (ha : orderOf a = p) (haZ : a ∈ Subgroup.normalizer (Z : Set Γ))
    (hfix : Z ⊓ Subgroup.centralizer {a} = ⊥) : Group.IsNilpotent Z := by
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hp.ne_one (by rw [← ha, orderOf_one])
  refine CFSG.BenderSuzuki.External.thompson_fixedPointFree_conjugation_nilpotent_subgroup
    Z (Subgroup.zpowers a) (Subgroup.zpowers_le.2 haZ) ⟨a, Subgroup.mem_zpowers a, ha1⟩ ?_
  intro x hx hx1
  have hord : orderOf x = p := by
    rcases (Nat.dvd_prime hp).1 (ha ▸ orderOf_dvd_of_mem_zpowers hx) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hax : a ∈ Subgroup.zpowers x := by
    have hzx : Subgroup.zpowers x = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, ha])
    exact hzx ▸ Subgroup.mem_zpowers a
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hax
  refine eq_bot_iff.2 fun y hy => ?_
  have hxy : Commute x y := (Subgroup.mem_centralizer_singleton_iff.1 hy.1).symm
  have hay : Commute a y := hm ▸ hxy.zpow_left m
  have : y ∈ Z ⊓ Subgroup.centralizer {a} :=
    ⟨hy.2, Subgroup.mem_centralizer_singleton_iff.2 hay.symm⟩
  rwa [hfix] at this

end CFSG.SignalizerFunctorTheorem.McBride.Thompson
