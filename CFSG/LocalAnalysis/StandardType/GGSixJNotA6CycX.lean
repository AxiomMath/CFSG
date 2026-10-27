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

namespace CFSG.StandardType

variable {G : Type*} [Group G]

theorem le_zpowers_of_isCyclic_of_pow_eq_one [Finite G] {p : ℕ} (hp : p.Prime) {K : Subgroup G}
    (hK : IsCyclic K) (hKp : ∀ c ∈ K, c ^ p = 1) {x : G} (hxK : x ∈ K) (hx1 : x ≠ 1) :
    K ≤ Subgroup.zpowers x := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hK.exists_generator
  have horder_g : orderOf g = Nat.card K := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    simpa using hKp (g : G) g.2
  have hcardK_dvd : Nat.card K ∣ p := horder_g ▸ orderOf_dvd_of_pow_eq_one hgp
  have hcardK_le : Nat.card K ≤ p := Nat.le_of_dvd hp.pos hcardK_dvd
  have horder_x : orderOf x = p := orderOf_eq_prime (hKp x hxK) hx1
  have hzx : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr hxK
  have hcard_le : Nat.card K ≤ Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, horder_x]
    exact hcardK_le
  have heq : Subgroup.zpowers x = K := Subgroup.eq_of_le_of_card_ge hzx hcard_le
  exact heq.ge

end CFSG.StandardType
