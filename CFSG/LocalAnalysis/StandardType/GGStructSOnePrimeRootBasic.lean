module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootDefs
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeCent
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TInd
public import CFSG.LocalAnalysis.StandardType.GGStructSOneHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.ChevTwo

section General

variable {C : Type} [Group C]

@[expose] def GGRootCentQLTyped (z : C) : Prop :=
  ∃ Q L : Subgroup C, IsPGroup 2 Q ∧ Q ⊔ L = Subgroup.centralizer ({z} : Set C) ∧
    L ≤ Subgroup.normalizer (Q : Set C) ∧ IsChevTwoLayered ↥L

theorem GGRootCentQLTyped.map {C' : Type} [Group C'] {z : C} (h : GGRootCentQLTyped z)
    (α : C ≃* C') : GGRootCentQLTyped (α z) := by
  obtain ⟨Q, L, hQ2, hQL, hLQ, hL⟩ := h
  refine ⟨Q.map α.toMonoidHom, L.map α.toMonoidHom, hQ2.map _, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hQL, RootCentExc.centralizer_map_mulEquiv]
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hLQ
  · exact IsChevTwoLayered.of_mulEquiv
      (L.equivMapOfInjective α.toMonoidHom α.injective).symm hL

theorem GGRootCentQLTyped.conj {z : C} (h : GGRootCentQLTyped z) (g : C) :
    GGRootCentQLTyped (g * z * g⁻¹) :=
  h.map (MulAut.conj g)

theorem GGRootCentQLTyped.of_conj {z g : C} (h : GGRootCentQLTyped (g * z * g⁻¹)) :
    GGRootCentQLTyped z := by
  have h' := h.conj g⁻¹
  rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h'

end General

section Tags

@[expose] def GGRootInvolCentTypedTag (t : CFSG.Open.StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X),
    CFSG.Open.StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → Subgroup.centralizer (ψ.range : Set X) = ⊥ →
    ∀ r : X, GGRootInvolution (ggU t n f).D t ψ r → GGInvolCentTyped ψ.range r

@[expose] def GGRootInvolModelTypedTag (t : CFSG.Open.StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X),
    CFSG.Open.StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → Subgroup.centralizer (ψ.range : Set X) = ⊥ →
    ∀ r : X, GGRootInvolution (ggU t n f).D t ψ r →
      ∃ (C : Type) (_ : Group C) (π : (ggU t n f).K →* C) (w : (ggU t n f).K),
        Function.Surjective π ∧ π.ker = ψ.ker ∧ ψ w = r ∧ GGRootCentQLTyped (π w)

@[expose] def GGRootInvolCentTypedInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (G₀ : Subgroup X) (r : X), IsSimpleGroup ↥G₀ →
    (∃ a b : ↥G₀, a * b ≠ b * a) → GGIsRootInvolution G₀ r → GGInvolCentTyped G₀ r

end Tags

end CFSG.StandardType
