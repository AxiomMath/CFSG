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

namespace CFSG.SignalizerFunctorTheorem

variable {H Q : Type*} [Group H] [Group Q]

noncomputable def quotientEquivOfKer {K₁ K₂ : Type*} [Group K₁] [Group K₂] (L₁ : Subgroup K₁)
    [L₁.Normal] (L₂ : Subgroup K₂) [L₂.Normal] (q : K₁ →* K₂ ⧸ L₂)
    (hq : Function.Surjective q) (hker : q.ker = L₁) : K₁ ⧸ L₁ ≃* K₂ ⧸ L₂ :=
  (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

theorem normal_comap_subgroupOf (π : H →* Q) {K L : Subgroup Q} (hLK : L ≤ K)
    [(L.subgroupOf K).Normal] : ((L.comap π).subgroupOf (K.comap π)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.comap_mono hLK)]
  intro l k hl hk
  have h := (Subgroup.normal_subgroupOf_iff hLK).mp inferInstance (π l) (π k) hl hk
  simpa using h

noncomputable def comapSectionEquiv (π : H →* Q) (hπ : Function.Surjective π)
    {K L : Subgroup Q} [(L.subgroupOf K).Normal]
    [((L.comap π).subgroupOf (K.comap π)).Normal] :
    (K.comap π) ⧸ (L.comap π).subgroupOf (K.comap π) ≃* K ⧸ L.subgroupOf K :=
  quotientEquivOfKer _ _ ((QuotientGroup.mk' (L.subgroupOf K)).comp (π.subgroupComap K))
    (by
      intro y
      obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨x, rfl⟩ := hπ k
      exact ⟨⟨x, hk⟩, rfl⟩)
    (by
      ext ⟨x, hx⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Iff.rfl)

variable {G : Type*} [Group G]

theorem normal_map_subgroupOf (ι : H →* G) {K L : Subgroup H}
    (hLK : L ≤ K) [(L.subgroupOf K).Normal] :
    ((L.map ι).subgroupOf (K.map ι)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hLK)]
  rintro _ _ ⟨l, hl, rfl⟩ ⟨k, hk, rfl⟩
  have h := (Subgroup.normal_subgroupOf_iff hLK).mp inferInstance l k hl hk
  exact ⟨k * l * k⁻¹, h, by simp⟩

noncomputable def mapSectionEquiv {ι : H →* G} (hι : Function.Injective ι) {K L : Subgroup H}
    [(L.subgroupOf K).Normal] [((L.map ι).subgroupOf (K.map ι)).Normal] :
    K ⧸ L.subgroupOf K ≃* (K.map ι) ⧸ (L.map ι).subgroupOf (K.map ι) :=
  quotientEquivOfKer _ _
    ((QuotientGroup.mk' ((L.map ι).subgroupOf (K.map ι))).comp
      (K.equivMapOfInjective ι hι).toMonoidHom)
    (by
      intro y
      obtain ⟨⟨_, k, hk, rfl⟩, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨⟨k, hk⟩, rfl⟩)
    (by
      ext ⟨x, hx⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_equivMapOfInjective_apply]
      exact Subgroup.mem_map_iff_mem hι)

end CFSG.SignalizerFunctorTheorem
