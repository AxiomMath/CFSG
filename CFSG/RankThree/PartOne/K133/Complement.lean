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

namespace CFSG.RankThree.PartOne.K133

open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {T E : Subgroup G} (hET : E ≤ Subgroup.normalizer (T : Set G))
    {w : G} (hw : w ∈ T ⊔ E) : ∃ τ ∈ T, ∃ a ∈ E, w = τ * a := by
  have hWset : ((T ⊔ E : Subgroup G) : Set G) = (E : Set G) * (T : Set G) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right E T hET
  have hw' : w ∈ (E : Set G) * (T : Set G) := hWset ▸ hw
  obtain ⟨a, ha, τ, hτ, rfl⟩ := hw'
  exact ⟨a * τ * a⁻¹, (Subgroup.mem_normalizer_iff.1 (hET ha) τ).1 hτ, a, ha, by group⟩

theorem exists_conj_of_complement [Finite G] {p : ℕ} (hp : p.Prime) {T E E' : Subgroup G}
    (hET : E ≤ Subgroup.normalizer (T : Set G)) (hE : IsPGroup p E) (hTp : ¬ p ∣ Nat.card T)
    (hE'W : E' ≤ T ⊔ E) (hcard : Nat.card E' = Nat.card E) :
    ∃ τ ∈ T, E' = E.map (MulAut.conj τ).toMonoidHom := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set W : Subgroup G := T ⊔ E with hW
  have hTW : T ≤ W := le_sup_left
  have hEW : E ≤ W := le_sup_right
  have hWdec : ∀ w ∈ W, ∃ τ ∈ T, ∃ a ∈ E, w = τ * a := fun w hw => exists_mul_of_mem_sup hET hw
  have hEWp : IsPGroup p (E.subgroupOf W) := hE.comap_subtype
  obtain ⟨Q, hEQ⟩ := hEWp.exists_le_sylow
  have hQE : (Q : Subgroup W) = E.subgroupOf W := by
    refine le_antisymm ?_ hEQ
    intro q hq
    obtain ⟨τ, hτ, a, ha, hqa⟩ := hWdec q.1 q.2
    have haQ : (⟨a, hEW ha⟩ : W) ∈ (Q : Subgroup W) := hEQ (Subgroup.mem_subgroupOf.2 ha)
    have hτQ : (⟨τ, hTW hτ⟩ : W) ∈ (Q : Subgroup W) := by
      have : (⟨τ, hTW hτ⟩ : W) = q * (⟨a, hEW ha⟩ : W)⁻¹ := Subtype.ext (by simp [hqa])
      rw [this]
      exact (Q : Subgroup W).mul_mem hq ((Q : Subgroup W).inv_mem haQ)
    have hτ1 : τ = 1 := by
      obtain ⟨k, hk⟩ := Q.isPGroup' (⟨⟨τ, hTW hτ⟩, hτQ⟩ : ↥(Q : Subgroup W))
      have hk' : τ ^ (p ^ k) = 1 := congrArg (fun z : W => (z : G)) (congrArg Subtype.val hk)
      have hd1 : orderOf (⟨τ, hτ⟩ : ↥T) ∣ p ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        exact Subtype.ext hk'
      have hd2 : orderOf (⟨τ, hτ⟩ : ↥T) ∣ Nat.card T := orderOf_dvd_natCard _
      have hcop : Nat.Coprime (p ^ k) (Nat.card T) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hTp)
      have : orderOf (⟨τ, hτ⟩ : ↥T) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
      exact congrArg Subtype.val (orderOf_eq_one_iff.1 this)
    rw [Subgroup.mem_subgroupOf]
    have : (q : G) = a := by rw [hqa, hτ1, one_mul]
    rw [this]
    exact ha
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE
  have hE'p : IsPGroup p E' := IsPGroup.of_card (hcard.trans hn)
  have hE'Wp : IsPGroup p (E'.subgroupOf W) := hE'p.comap_subtype
  obtain ⟨S, hS⟩ := hE'Wp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W Q S
  have hconj : ∀ x ∈ E', (g : G)⁻¹ * x * g ∈ E := by
    intro x hx
    have hxS : (⟨x, hE'W hx⟩ : W) ∈ (S : Subgroup W) := hS (Subgroup.mem_subgroupOf.2 hx)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hQE] at hxS
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv] at hxS
    exact Subgroup.mem_subgroupOf.1 hxS
  have hle : E' ≤ E.map (MulAut.conj (g : G)).toMonoidHom := by
    intro x hx
    exact Subgroup.mem_map.2 ⟨(g : G)⁻¹ * x * g, hconj x hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hEg : E' = E.map (MulAut.conj (g : G)).toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective, hcard]
  obtain ⟨τ₀, hτ₀, a₀, ha₀, hgτ⟩ := hWdec g.1 g.2
  refine ⟨τ₀, hτ₀, ?_⟩
  have h1 : E.map (MulAut.conj a₀).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer ha₀)
  have hcomp : (MulAut.conj (τ₀ * a₀)).toMonoidHom =
      (MulAut.conj τ₀).toMonoidHom.comp (MulAut.conj a₀).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hEg, hgτ, hcomp, ← Subgroup.map_map, h1]

end CFSG.RankThree.PartOne.K133
