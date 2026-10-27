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

namespace CFSG.Monster.B.TwoA.Amalgam

variable {G M Q : Type*} [Group G] [Group M] [Group Q]

theorem exists_surj_of_mulEquiv_quotient (p : G →* M) (ρ : Q →* M) {A : Subgroup G}
    {S : Subgroup Q} {N : Subgroup S} [N.Normal] (e : A ≃* S ⧸ N)
    (he : ∀ (z : A) (g : S), e z = QuotientGroup.mk g ↔ p (z : G) = ρ (g : Q)) :
    ∃ φ : S →* A, Function.Surjective φ ∧ ∀ g : S, p (φ g : G) = ρ (g : Q) := by
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' N), fun z => ?_, fun g => ?_⟩
  · obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e z)
    exact ⟨g, by
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hg, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply]⟩
  · refine (he _ g).1 ?_
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]

theorem exists_surj_of_mulEquiv_quotient_subgroupOf {D : Type*} [Group D] {E P : Subgroup D}
    (hPE : P ≤ E) (p : G →* M) (ρ : E →* M) {A : Subgroup G} {N : Subgroup (P.subgroupOf E)}
    [N.Normal] (e : A ≃* P.subgroupOf E ⧸ N)
    (he : ∀ (z : A) (g : P.subgroupOf E), e z = QuotientGroup.mk g ↔ p (z : G) = ρ (g : E)) :
    ∃ φ : P →* A, Function.Surjective φ ∧
      ∀ g : P, p (φ g : G) = ρ (Subgroup.inclusion hPE g) := by
  obtain ⟨φ, hφ, hpφ⟩ := exists_surj_of_mulEquiv_quotient p ρ e he
  refine ⟨φ.comp (Subgroup.subgroupOfEquivOfLe hPE).symm.toMonoidHom,
    hφ.comp (Subgroup.subgroupOfEquivOfLe hPE).symm.surjective, fun g => ?_⟩
  have hg : (((Subgroup.subgroupOfEquivOfLe hPE).symm g : P.subgroupOf E) : E) =
      Subgroup.inclusion hPE g :=
    Subtype.ext (Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe hPE g)
  exact (hpφ _).trans (congrArg ρ hg)

theorem eq_of_mulEquiv_quotient (p : G →* M) (ρ : Q →* M) {A : Subgroup G} {S : Subgroup Q}
    {N : Subgroup S} [N.Normal] (e : A ≃* S ⧸ N)
    (he : ∀ (z : A) (g : S), e z = QuotientGroup.mk g ↔ p (z : G) = ρ (g : Q))
    {z z' : A} (h : p (z : G) = p (z' : G)) : z = z' := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e z)
  have h1 : p (z : G) = ρ (g : Q) := (he z g).1 hg.symm
  have h2 : e z' = QuotientGroup.mk g := (he z' g).2 (h.symm.trans h1)
  exact e.injective (hg.symm.trans h2.symm)

theorem exists_of_mulEquiv_quotient (p : G →* M) (ρ : Q →* M) {A : Subgroup G}
    {S : Subgroup Q} {N : Subgroup S} [N.Normal] (e : A ≃* S ⧸ N)
    (he : ∀ (z : A) (g : S), e z = QuotientGroup.mk g ↔ p (z : G) = ρ (g : Q)) :
    (∀ z ∈ A, ∃ g : S, p z = ρ (g : Q)) ∧ ∀ g : S, ∃ z ∈ A, p z = ρ (g : Q) := by
  refine ⟨fun z hz => ?_, fun g => ⟨e.symm (QuotientGroup.mk g), (e.symm _).2,
    (he _ g).1 (e.apply_symm_apply _)⟩⟩
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e ⟨z, hz⟩)
  exact ⟨g, (he _ g).1 hg.symm⟩

theorem subgroupOf_eq_map_of_lift {R : Type*} [Group R] (p : G →* M) {A A' : Subgroup G}
    (hA' : A' ≤ A) (hinj : ∀ z z' : A, p (z : G) = p (z' : G) → z = z') {ρ : R → M}
    {φ : R →* A} (hφ : ∀ g, p (φ g : G) = ρ g) {B : Subgroup R}
    (h1 : ∀ z ∈ A', ∃ g ∈ B, p z = ρ g) (h2 : ∀ g ∈ B, ∃ z ∈ A', p z = ρ g) :
    A'.subgroupOf A = B.map φ := by
  ext z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro hz
    obtain ⟨g, hg, hpg⟩ := h1 z hz
    exact ⟨g, hg, hinj _ _ ((hφ g).trans hpg.symm)⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨w, hw, hpw⟩ := h2 g hg
    have h : (⟨w, hA' hw⟩ : A) = φ g := hinj _ _ (hpw.trans (hφ g).symm)
    rw [← h]
    exact hw

end CFSG.Monster.B.TwoA.Amalgam
