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
public import Mathlib.GroupTheory.Nilpotent
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

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Recog

open scoped Pointwise

variable {G : Type*} [Group G]

theorem natCard_centralizer_conj (g x : G) :
    Nat.card (Subgroup.centralizer {g * x * g⁻¹}) = Nat.card (Subgroup.centralizer {x}) := by
  refine Nat.card_congr
    { toFun := fun z => ⟨g⁻¹ * z * g, ?_⟩
      invFun := fun z => ⟨g * z * g⁻¹, ?_⟩
      left_inv := fun z => Subtype.ext (by simp only; group)
      right_inv := fun z => Subtype.ext (by simp only; group) }
  · have hz := Subgroup.mem_centralizer_singleton_iff.1 z.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * z * g * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * z) * g := by rw [hz]
      _ = x * (g⁻¹ * z * g) := by group
  · have hz := Subgroup.mem_centralizer_singleton_iff.1 z.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hz]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group

theorem relIndex_mul_natCard [Finite G] {T K : Subgroup G} (hTK : T ≤ K) :
    T.relIndex K * Nat.card T = Nat.card K := by
  have h := (T.subgroupOf K).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv] at h
  rw [Subgroup.relIndex, mul_comm]
  exact h

theorem exists_mem_normalizer_conj_eq [Finite G] {p : ℕ} [Fact p.Prime] {T : Subgroup G}
    (hT : IsPGroup p T) {x y : G} (hTx : T ≤ Subgroup.centralizer {x})
    (hTy : T ≤ Subgroup.centralizer {y}) (hpx : ¬ p ∣ T.relIndex (Subgroup.centralizer {x}))
    (hxy : IsConj x y) :
    ∃ n ∈ Subgroup.normalizer (T : Set G), n * x * n⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hxy
  set C := Subgroup.centralizer {y} with hC
  set T' := T.map (MulAut.conj g).toMonoidHom with hT'
  have hconj : ∀ t : G, (MulAut.conj g).toMonoidHom t = g * t * g⁻¹ := fun t => rfl
  have hT'C : T' ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    have htx := Subgroup.mem_centralizer_singleton_iff.1 (hTx ht)
    rw [hconj, hC, Subgroup.mem_centralizer_singleton_iff, ← hg]
    calc g * t * g⁻¹ * (g * x * g⁻¹) = g * (t * x) * g⁻¹ := by group
      _ = g * (x * t) * g⁻¹ := by rw [htx]
      _ = g * x * g⁻¹ * (g * t * g⁻¹) := by group
  have hcardT' : Nat.card T' = Nat.card T :=
    (Nat.card_congr (T.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm
  have hcardC : Nat.card C = Nat.card (Subgroup.centralizer {x}) := by
    rw [hC, ← hg]
    exact natCard_centralizer_conj g x
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hi1 : T.relIndex C = T.relIndex (Subgroup.centralizer {x}) := by
    have e1 := relIndex_mul_natCard hTy
    have e2 := relIndex_mul_natCard hTx
    rw [hcardC, ← e2] at e1
    exact Nat.eq_of_mul_eq_mul_right hpos e1
  have hi2 : T'.relIndex C = T.relIndex (Subgroup.centralizer {x}) := by
    have e1 := relIndex_mul_natCard hT'C
    have e2 := relIndex_mul_natCard hTx
    rw [hcardT', hcardC, ← e2] at e1
    exact Nat.eq_of_mul_eq_mul_right hpos e1
  have hP1 : IsPGroup p (T.subgroupOf C) := hT.comap_of_injective C.subtype Subtype.val_injective
  have hP2 : IsPGroup p (T'.subgroupOf C) :=
    (hT.map (MulAut.conj g).toMonoidHom).comap_of_injective C.subtype Subtype.val_injective
  have hn1 : ¬ p ∣ (T.subgroupOf C).index := by
    rw [← Subgroup.relIndex, hi1]
    exact hpx
  have hn2 : ¬ p ∣ (T'.subgroupOf C).index := by
    rw [← Subgroup.relIndex, hi2]
    exact hpx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (hP2.toSylow hn2) (hP1.toSylow hn1)
  have hcS : MulAut.conj c • T'.subgroupOf C = T.subgroupOf C := by
    have h := congrArg (fun P : Sylow p C => (P : Subgroup C)) hc
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
    exact h
  have hc' : ∀ z : C, z ∈ T'.subgroupOf C → c * z * c⁻¹ ∈ T.subgroupOf C := by
    intro z hz
    rw [← hcS]
    have h := Subgroup.smul_mem_pointwise_smul z (MulAut.conj c) (T'.subgroupOf C) hz
    rwa [MulAut.smul_def, MulAut.conj_apply] at h
  have hc'' : ∀ z : C, z ∈ T.subgroupOf C → c⁻¹ * z * c ∈ T'.subgroupOf C := by
    intro z hz
    rw [← hcS, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv,
      MulAut.conj_apply, inv_inv] at hz
    exact hz
  refine ⟨(c : G) * g, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have hz : g * t * g⁻¹ ∈ T' := ⟨t, ht, rfl⟩
      have h1 := hc' ⟨g * t * g⁻¹, hT'C hz⟩ (Subgroup.mem_subgroupOf.2 hz)
      rw [Subgroup.mem_subgroupOf] at h1
      have e : (c : G) * g * t * ((c : G) * g)⁻¹ = c * (g * t * g⁻¹) * (c : G)⁻¹ := by group
      rw [e]
      exact h1
    · intro ht
      have hz : (c : G) * g * t * ((c : G) * g)⁻¹ ∈ C := by
        have e : (c : G) * g * t * ((c : G) * g)⁻¹ ∈ T := ht
        exact hTy e
      have h1 := hc'' ⟨_, hz⟩ (Subgroup.mem_subgroupOf.2 ht)
      rw [Subgroup.mem_subgroupOf] at h1
      have e : ((c⁻¹ * ⟨_, hz⟩ * c : C) : G) = g * t * g⁻¹ := by
        show (c : G)⁻¹ * ((c : G) * g * t * ((c : G) * g)⁻¹) * c = g * t * g⁻¹
        group
      rw [e] at h1
      obtain ⟨t', ht', e'⟩ := h1
      have e'' : t' = t := by
        have := congrArg (fun w => g⁻¹ * w * g) e'
        simp only [hconj] at this
        rw [show g⁻¹ * (g * t' * g⁻¹) * g = t' by group,
          show g⁻¹ * (g * t * g⁻¹) * g = t by group] at this
        exact this
      rw [← e'']
      exact ht'
  · have hcy : (c : G) * y = y * c := Subgroup.mem_centralizer_singleton_iff.1 c.2
    calc (c : G) * g * x * ((c : G) * g)⁻¹ = c * (g * x * g⁻¹) * (c : G)⁻¹ := by group
      _ = c * y * (c : G)⁻¹ := by rw [hg]
      _ = y := by rw [hcy, mul_inv_cancel_right]

theorem exists_mem_normalizer_conj_eq_of_mem_center [Finite G] {p : ℕ} [Fact p.Prime]
    {T : Subgroup G} (hT : IsPGroup p T) {x y : G}
    (_hx : x ∈ T ⊓ Subgroup.centralizer (T : Set G))
    (_hy : y ∈ T ⊓ Subgroup.centralizer (T : Set G))
    (hTx : T ≤ Subgroup.centralizer {x}) (hTy : T ≤ Subgroup.centralizer {y})
    (hpx : ¬ p ∣ T.relIndex (Subgroup.centralizer {x}))
    (_hpy : ¬ p ∣ T.relIndex (Subgroup.centralizer {y})) (hxy : IsConj x y) :
    ∃ n ∈ Subgroup.normalizer (T : Set G), n * x * n⁻¹ = y :=
  exists_mem_normalizer_conj_eq hT hTx hTy hpx hxy

end CFSG.Monster.B.Recog
