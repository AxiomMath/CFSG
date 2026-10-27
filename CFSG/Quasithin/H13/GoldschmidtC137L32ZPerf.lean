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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem cocycle_mem_commutator_of_perfect {L Z : Subgroup G}
    (hLZ : L ≤ normalizer (Z : Set G)) (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hL : Group.IsPerfect ↥L) {z : G} (hc : ∀ k ∈ L, k * z * k⁻¹ * z⁻¹ ∈ Z) :
    ∀ k ∈ L, k * z * k⁻¹ * z⁻¹ ∈ ⁅Z, L⁆ := by
  classical
  set U : Subgroup G := ⁅Z, L⁆ with hU
  have hUZ : U ≤ Z := Subgroup.le_normalizer_iff_commutator_le_left.mp hLZ
  have conj_triv : ∀ a ∈ Z, ∀ b ∈ Z, a⁻¹ * b * a = b := by
    intro a ha b hb
    rw [mul_assoc, hZ b hb a ha, inv_mul_cancel_left]
  set U' : Subgroup ↥Z := U.subgroupOf Z with hU'
  have hU'n : U'.Normal := ⟨fun n hn g => by
    have h1 : (g : ↥Z) * n * g⁻¹ = n := Subtype.ext (by
      show (g : G) * (n : G) * (g : G)⁻¹ = n
      rw [hZ _ g.2 _ n.2]
      group)
    rw [h1]
    exact hn⟩
  let c : ↥L → ↥Z := fun k => ⟨k * z * k⁻¹ * z⁻¹, hc k k.2⟩
  have hcval : ∀ k : ↥L, ((c k : ↥Z) : G) = (k : G) * z * (k : G)⁻¹ * z⁻¹ := fun _ => rfl
  have hact : ∀ (k : ↥L) (y : ↥Z), (k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ ∈ U := by
    intro k y
    have h1 : ⁅(k : G), (y : G)⁆ ∈ ⁅L, Z⁆ := Subgroup.commutator_mem_commutator k.2 y.2
    rw [Subgroup.commutator_comm] at h1
    simpa [commutatorElement_def] using h1
  have aux : ∀ (k₁ c₁ c₂ : G), c₁ ∈ Z → c₂ ∈ Z → k₁ * c₂ * k₁⁻¹ * c₂⁻¹ ∈ U →
      (c₁ * c₂)⁻¹ * ((k₁ * c₂ * k₁⁻¹) * c₁) ∈ U := by
    intro k₁ c₁ c₂ hc₁ hc₂ hd
    have hdZ := hUZ hd
    have e1 : k₁ * c₂ * k₁⁻¹ = (k₁ * c₂ * k₁⁻¹ * c₂⁻¹) * c₂ := by group
    have key : (c₁ * c₂)⁻¹ * ((k₁ * c₂ * k₁⁻¹) * c₁) = k₁ * c₂ * k₁⁻¹ * c₂⁻¹ := by
      generalize hdd : k₁ * c₂ * k₁⁻¹ * c₂⁻¹ = d at e1 hdZ ⊢
      rw [e1]
      calc (c₁ * c₂)⁻¹ * (d * c₂ * c₁) = c₂⁻¹ * (c₁⁻¹ * (d * c₂) * c₁) := by group
        _ = c₂⁻¹ * (d * c₂) := by rw [conj_triv c₁ hc₁ (d * c₂) (Z.mul_mem hdZ hc₂)]
        _ = d := by
          have := conj_triv c₂ hc₂ d hdZ
          simpa [mul_assoc] using this
    rw [key]
    exact hd
  let f : ↥L →* ↥Z ⧸ U' :=
    { toFun := fun k => QuotientGroup.mk (c k)
      map_one' := by
        have h1 : c 1 = 1 := Subtype.ext (by rw [hcval]; simp)
        rw [h1]
        rfl
      map_mul' := fun k₁ k₂ => by
        show (QuotientGroup.mk (c (k₁ * k₂)) : ↥Z ⧸ U') =
          QuotientGroup.mk (c k₁) * QuotientGroup.mk (c k₂)
        rw [← QuotientGroup.mk_mul]
        symm
        rw [QuotientGroup.eq, hU', Subgroup.mem_subgroupOf]
        have e2 : ((c (k₁ * k₂) : ↥Z) : G) = ((k₁ : G) * ((c k₂ : ↥Z) : G) * (k₁ : G)⁻¹) *
            ((c k₁ : ↥Z) : G) := by
          rw [hcval, hcval, hcval]
          simp only [Subgroup.coe_mul, mul_inv_rev]
          group
        have e3 : (((c k₁ * c k₂)⁻¹ * c (k₁ * k₂) : ↥Z) : G) =
            (((c k₁ : ↥Z) : G) * ((c k₂ : ↥Z) : G))⁻¹ * ((c (k₁ * k₂) : ↥Z) : G) := rfl
        rw [e3, e2]
        exact aux k₁ _ _ (c k₁).2 (c k₂).2 (hact k₁ (c k₂)) }
  have hcomm : ∀ a b : ↥L, ⁅f a, f b⁆ = 1 := by
    intro a b
    rw [commutatorElement_eq_one_iff_mul_comm]
    show (QuotientGroup.mk (c a) : ↥Z ⧸ U') * QuotientGroup.mk (c b) =
      QuotientGroup.mk (c b) * QuotientGroup.mk (c a)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hZ _ (c a).2 _ (c b).2)
  have hle : commutator ↥L ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, hcomm]
  intro k hk
  have h1 : (⟨k, hk⟩ : ↥L) ∈ commutator ↥L := by
    rw [Group.isPerfect_def.1 hL]
    trivial
  have h2 : f ⟨k, hk⟩ = 1 := MonoidHom.mem_ker.1 (hle h1)
  have h3 : (QuotientGroup.mk (c ⟨k, hk⟩) : ↥Z ⧸ U') = 1 := h2
  rw [QuotientGroup.eq_one_iff, hU', Subgroup.mem_subgroupOf] at h3
  exact h3

end CFSG.Quasithin.H13.U3.GC137
