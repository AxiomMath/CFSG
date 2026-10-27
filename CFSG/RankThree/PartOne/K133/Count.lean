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

namespace CFSG.RankThree.PartOne.K133

variable {G : Type} [Group G]

theorem card_sup_of_commute_disjoint {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hdisj : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hcomm' : ∀ (m : ↥H) (n : ↥K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => hcomm m.1 m.2 n.1 n.2
  let φ := MonoidHom.noncommCoprod H.subtype K.subtype hcomm'
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 hdisj
  have hrange : φ.range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem card_sup_zpowers {Y : Subgroup G} {b : G} {p : ℕ} (hp : p.Prime) (hb : orderOf b = p)
    (hcomm : ∀ y ∈ Y, y * b = b * y) (hbY : b ∉ Y) :
    Nat.card ↥(Y ⊔ Subgroup.zpowers b) = Nat.card Y * p := by
  have : Fact p.Prime := ⟨hp⟩
  have hcardz : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hb]
  have hdisj : Y ⊓ Subgroup.zpowers b = ⊥ := by
    have hfact : Fact (Nat.card (Subgroup.zpowers b)).Prime := ⟨by rw [hcardz]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Y.subgroupOf (Subgroup.zpowers b)) with h | h
    · exact disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h)
    · exact absurd ((Subgroup.subgroupOf_eq_top.1 h) (Subgroup.mem_zpowers b)) hbY
  rw [card_sup_of_commute_disjoint ?_ hdisj, hcardz]
  intro y hy z hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ((Commute.zpow_right (show Commute y b from hcomm y hy) n)).eq

theorem exists_subgroup_card_between [Finite G] {p : ℕ} (hp : p.Prime) {D X : Subgroup G}
    (hXD : X ≤ D) {a : ℕ} (hX : Nat.card X = p ^ a) {n : ℕ} (han : a ≤ n)
    (hDn : p ^ n ∣ Nat.card D) :
    ∃ Y : Subgroup G, X ≤ Y ∧ Y ≤ D ∧ Nat.card Y = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  induction n, han using Nat.le_induction with
  | base => exact ⟨X, le_rfl, hXD, hX⟩
  | succ n han ih =>
    obtain ⟨Y, hXY, hYD, hY⟩ := ih ((pow_dvd_pow p (Nat.le_succ n)).trans hDn)
    have hYsub : Nat.card (Y.subgroupOf D) = p ^ n := by
      rw [← hY]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYD).toEquiv
    obtain ⟨K, hK, hYK⟩ := Sylow.exists_subgroup_card_pow_succ hDn hYsub
    refine ⟨K.map D.subtype, ?_, Subgroup.map_subtype_le K, ?_⟩
    · intro x hx
      have hxY := hXY hx
      have hxD := hYD hxY
      have : (⟨x, hxD⟩ : ↥D) ∈ Y.subgroupOf D := hxY
      exact ⟨⟨x, hxD⟩, hYK this, rfl⟩
    · rw [Subgroup.card_map_of_injective D.subtype_injective, hK]

end CFSG.RankThree.PartOne.K133
