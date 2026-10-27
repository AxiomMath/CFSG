module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.C3AlgebraicPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3AlgebraicPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.B3Algebraic
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.Symplectic CFSG.Open CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.StandardType.F4ExplicitPos.FiniteAction CFSG.StandardType.F4ExplicitPos.B3Pinned
  CFSG.StandardType.F4ExplicitPos.B3Exact CFSG.StandardType.F4ExplicitPos.B3Faithful
  CFSG.StandardType.F4ExplicitPos.B3Unconditional
  C3Range C3Algebraic B2Finite
  CFSG.Timmesfeld.LieEmbed

section Algebraic
variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem f4_exponent_eq_relationExponent_zero (i : Fin F4.tag.rank) :
    F4.exponent i = F4.relationExponent 0 i := by
  simp [ReeTag.exponent, ReeTag.relationExponent]

theorem pinnedFamilySign_eq_one_charTwo
    (K : Type) [Field K] [CharP K 2]
    (α : Fin F4.tag.rank → ℤ) :
    ((rootOperatorFamily .F4).pinnedFamilySign α : K) = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg : (-1 : K) = 1 := by linear_combination -h2
  rcases (rootOperatorFamily .F4).pinnedFamilySign_eq α with h | h
  · rw [h]; norm_num
  · rw [h]; simp only [Int.cast_neg, Int.cast_one]; exact hneg

theorem exists_sq_eq_charTwo_algebraic (c : Ω) : ∃ d : Ω, d ^ 2 = c := by
  obtain ⟨k, hk, hc⟩ := TauCeti.exists_mem_frobeniusFixedSubfield Ω 2 c
  have : Finite ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) :=
    TauCeti.finite_frobeniusFixedSubfield Ω 2 k hk
  have : CharP ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) 2 :=
    Subfield.charP (TauCeti.frobeniusFixedSubfield Ω 2 k) 2
  obtain ⟨d, hd⟩ :=
    CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exists_sq_eq_charTwo_narrow
      (K := ↥(TauCeti.frobeniusFixedSubfield Ω 2 k)) ⟨c, hc⟩
  refine ⟨(TauCeti.frobeniusFixedSubfield Ω 2 k).subtype d, ?_⟩
  rw [← map_pow, hd]
  rfl

theorem j_pinnedX
    {E : Type} [Field E] [CharP E 2] (f : E →+* Ω)
    (α : Fin F4.tag.rank → ℤ) (c : E) :
    j (τ := F4.tag) f
        (⟨pinnedX F4.tag E α c, pinnedX_mem_adjointGroup α c⟩ : adjointGroup F4.tag E) =
      ⟨pinnedX F4.tag Ω α (f c), pinnedX_mem_adjointGroup α (f c)⟩ := by
  refine Subtype.ext ?_
  rw [j_apply]
  change bcGL (τ := F4.tag) f (pinnedX F4.tag E α c) = pinnedX F4.tag Ω α (f c)
  rw [bcGL_pinnedX]

theorem sigmaΩ_pinnedX
    {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) (c : Ω) :
    (sigmaΩ Ω) (⟨pinnedX F4.tag Ω α c, pinnedX_mem_adjointGroup α c⟩ : adjointGroup F4.tag Ω) =
      ⟨pinnedX F4.tag Ω (F4.dualRoot α) (c ^ F4.exponent (pinnedData F4.tag α).1),
        pinnedX_mem_adjointGroup _ _⟩ := by
  obtain ⟨k, hk, hc⟩ := TauCeti.exists_mem_frobeniusFixedSubfield Ω 2 c
  have : Finite ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) :=
    TauCeti.finite_frobeniusFixedSubfield Ω 2 k hk
  have : CharP ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) 2 :=
    Subfield.charP (TauCeti.frobeniusFixedSubfield Ω 2 k) 2
  set E := TauCeti.frobeniusFixedSubfield Ω 2 k
  set cE : E := ⟨c, hc⟩
  have hx : (⟨pinnedX F4.tag Ω α c, pinnedX_mem_adjointGroup α c⟩ : adjointGroup F4.tag Ω) =
      j (τ := F4.tag) E.subtype
        (⟨pinnedX F4.tag E α cE, pinnedX_mem_adjointGroup α cE⟩ : adjointGroup F4.tag E) := by
    refine Subtype.ext ?_
    rw [j_apply]
    change pinnedX F4.tag Ω α c =
      bcGL (τ := F4.tag) E.subtype (pinnedX F4.tag E α cE)
    rw [bcGL_pinnedX]
    rfl
  calc (sigmaΩ Ω) ⟨pinnedX F4.tag Ω α c, pinnedX_mem_adjointGroup α c⟩
      = (sigmaΩ Ω) (j (τ := F4.tag) E.subtype
          ⟨pinnedX F4.tag E α cE, pinnedX_mem_adjointGroup α cE⟩) := by rw [hx]
    _ = j (τ := F4.tag) E.subtype (B3Unconditional.f4_exceptionalEndo E
          ⟨pinnedX F4.tag E α cE, pinnedX_mem_adjointGroup α cE⟩) := by
          rw [f4Endo_natural Ω E.subtype
            ⟨pinnedX F4.tag E α cE, pinnedX_mem_adjointGroup α cE⟩]
    _ = j (τ := F4.tag) E.subtype
          ⟨pinnedX F4.tag E (F4.dualRoot α)
            (cE ^ F4.exponent (pinnedData F4.tag α).1), pinnedX_mem_adjointGroup _ _⟩ := by
          rw [CFSG.StandardType.F4ExplicitPos.B3Pinned.f4_exceptionalEndo_pinnedX hα cE]
    _ = ⟨pinnedX F4.tag Ω (F4.dualRoot α)
          (c ^ F4.exponent (pinnedData F4.tag α).1), pinnedX_mem_adjointGroup _ _⟩ := by
          rw [j_pinnedX]
          congr 1

theorem sigmaΩ_pinnedX_long
    {α : Fin F4.tag.rank → ℤ}
    (hα : α ∈ F4.longRoots) (c : Ω) :
    (sigmaΩ Ω) (⟨pinnedX F4.tag Ω α c, pinnedX_mem_adjointGroup α c⟩ : adjointGroup F4.tag Ω) =
      ⟨pinnedX F4.tag Ω (F4.dualRoot α) c, pinnedX_mem_adjointGroup _ _⟩ := by
  have hb : F4.exponent (pinnedData F4.tag α).1 = 1 := by
    have h := (ReeTag.relationExponent_pinnedData_F4 (a := 0) hα.1).1 hα
    rw [← f4_exponent_eq_relationExponent_zero, pow_zero] at h
    exact h
  calc (sigmaΩ Ω) ⟨pinnedX F4.tag Ω α c, pinnedX_mem_adjointGroup α c⟩
      = ⟨pinnedX F4.tag Ω (F4.dualRoot α)
            (c ^ F4.exponent (pinnedData F4.tag α).1), pinnedX_mem_adjointGroup _ _⟩ :=
        sigmaΩ_pinnedX Ω hα.1 c
    _ = ⟨pinnedX F4.tag Ω (F4.dualRoot α) c, pinnedX_mem_adjointGroup _ _⟩ := by
        rw [hb, pow_one]

theorem sigmaΩ_pinnedX_short
    {α : Fin F4.tag.rank → ℤ}
    (hα : α ∈ F4.shortRoots) (c : Ω) :
    (sigmaΩ Ω) (⟨pinnedX F4.tag Ω α c, pinnedX_mem_adjointGroup α c⟩ : adjointGroup F4.tag Ω) =
      ⟨pinnedX F4.tag Ω (F4.dualRoot α) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  have hb : F4.exponent (pinnedData F4.tag α).1 = 2 := by
    have h := (ReeTag.relationExponent_pinnedData_F4 (a := 0) hα.1).2 hα
    rw [← f4_exponent_eq_relationExponent_zero, pow_zero, mul_one] at h
    exact h
  calc (sigmaΩ Ω) ⟨pinnedX F4.tag Ω α c, pinnedX_mem_adjointGroup α c⟩
      = ⟨pinnedX F4.tag Ω (F4.dualRoot α)
            (c ^ F4.exponent (pinnedData F4.tag α).1), pinnedX_mem_adjointGroup _ _⟩ :=
        sigmaΩ_pinnedX Ω hα.1 c
    _ = ⟨pinnedX F4.tag Ω (F4.dualRoot α) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
        rw [hb]

theorem sigmaΩ_eq_one
    {g : adjointGroup .F4 Ω} (hg : (sigmaΩ Ω) g = 1) : g = 1 := by
  obtain ⟨k, hk, gE, hgE⟩ := f4_exists_finite_subfield_preimage Ω g
  have : Finite ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) :=
    TauCeti.finite_frobeniusFixedSubfield Ω 2 k hk
  have : CharP ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) 2 :=
    Subfield.charP (TauCeti.frobeniusFixedSubfield Ω 2 k) 2
  have h1 : j (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype
      (CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo
        (TauCeti.frobeniusFixedSubfield Ω 2 k) gE) = 1 := by
    have hnat : j (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype
        (CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo
          (TauCeti.frobeniusFixedSubfield Ω 2 k) gE) =
        (sigmaΩ Ω) (j (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype gE) := by
      exact f4Endo_natural Ω (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype gE
    rw [hnat, hgE, hg]
    rfl
  have h2 : CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo
      (TauCeti.frobeniusFixedSubfield Ω 2 k) gE = 1 :=
    j_injective (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype
      (RingHom.injective _)
      (h1.trans (map_one (j (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype)).symm)
  have h3 : gE = 1 :=
    (CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo_bijective
      (TauCeti.frobeniusFixedSubfield Ω 2 k)).1
      (h2.trans (map_one (CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo
        (TauCeti.frobeniusFixedSubfield Ω 2 k))).symm)
  rw [← hgE, h3, map_one]

theorem sigmaΩ_injective :
    Function.Injective (sigmaΩ Ω) := by
  intro a b hab
  have h : a * b⁻¹ = 1 := sigmaΩ_eq_one Ω (by rw [map_mul, map_inv, hab, mul_inv_cancel])
  rwa [mul_inv_eq_one] at h

theorem sigmaΩ_surjective :
    Function.Surjective (sigmaΩ Ω) := by
  intro y
  obtain ⟨k, hk, yE, hyE⟩ := f4_exists_finite_subfield_preimage Ω y
  have : Finite ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) :=
    TauCeti.finite_frobeniusFixedSubfield Ω 2 k hk
  have : CharP ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) 2 :=
    Subfield.charP (TauCeti.frobeniusFixedSubfield Ω 2 k) 2
  obtain ⟨xE, hxE⟩ :=
    (CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo_bijective
      (TauCeti.frobeniusFixedSubfield Ω 2 k)).2 yE
  refine ⟨j (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype xE, ?_⟩
  have hnat : (sigmaΩ Ω) ((j (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype) xE) =
      j (τ := .F4) (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype
        (CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalEndo
          (TauCeti.frobeniusFixedSubfield Ω 2 k) xE) := by
    exact (f4Endo_natural Ω (TauCeti.frobeniusFixedSubfield Ω 2 k).subtype xE).symm
  rw [hnat, hxE, hyE]

theorem sigmaΩ_bijective :
    Function.Bijective (sigmaΩ Ω) :=
  ⟨sigmaΩ_injective Ω, sigmaΩ_surjective Ω⟩

end Algebraic

section B3

variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

abbrev sigmaΩF4 :
    adjointGroup .F4 Ω →* adjointGroup .F4 Ω :=
  sigmaΩ Ω

abbrev iBΩ
    : StatedSp 3 Ω →* adjointGroup .F4 Ω :=
  (sigmaΩF4 Ω).comp (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω)

theorem sigmaΩF4_f4Par
    {α : Fin (Tag.rank .F4) → ℤ} (hα : IsRoot .F4 α) (c : Ω) :
    (sigmaΩF4 Ω) (Adjoint.f4Par Ω α c) =
      Adjoint.f4Par Ω (F4.dualRoot α) (c ^ F4.exponent (pinnedData F4.tag α).1) := by
  have hsign : ((rootOperatorFamily .F4).pinnedFamilySign α : Ω) = 1 :=
    pinnedFamilySign_eq_one_charTwo Ω α
  have h1 : Adjoint.f4Par Ω α c =
      ⟨pinnedX F4.tag Ω α (((rootOperatorFamily .F4).pinnedFamilySign α : Ω) * c),
        pinnedX_mem_adjointGroup _ _⟩ :=
    Subtype.ext (CFSG.StandardType.F4ExplicitPos.C3Algebraic.f4Par_coe_eq_pinnedX_alg (K := Ω) hα c)
  have h2 : (sigmaΩF4 Ω) (Adjoint.f4Par Ω α c) =
      (sigmaΩ Ω) ⟨pinnedX F4.tag Ω α
        (((rootOperatorFamily .F4).pinnedFamilySign α : Ω) * c),
        pinnedX_mem_adjointGroup _ _⟩ := by rw [h1]; rfl
  have h3 : (sigmaΩ Ω) (⟨pinnedX F4.tag Ω α
        (((rootOperatorFamily .F4).pinnedFamilySign α : Ω) * c),
        pinnedX_mem_adjointGroup _ _⟩ : adjointGroup F4.tag Ω) =
      (⟨pinnedX F4.tag Ω (F4.dualRoot α)
        ((((rootOperatorFamily .F4).pinnedFamilySign α : Ω) * c)
          ^ F4.exponent (pinnedData F4.tag α).1), pinnedX_mem_adjointGroup _ _⟩ :
            adjointGroup F4.tag Ω) :=
    sigmaΩ_pinnedX Ω hα (((rootOperatorFamily .F4).pinnedFamilySign α : Ω) * c)
  have h4 : (⟨pinnedX F4.tag Ω (F4.dualRoot α)
        ((((rootOperatorFamily .F4).pinnedFamilySign α : Ω) * c)
          ^ F4.exponent (pinnedData F4.tag α).1), pinnedX_mem_adjointGroup _ _⟩ :
            adjointGroup F4.tag Ω) =
      (⟨pinnedX F4.tag Ω (F4.dualRoot α)
        (c ^ F4.exponent (pinnedData F4.tag α).1), pinnedX_mem_adjointGroup _ _⟩ :
            adjointGroup F4.tag Ω) := by
    rw [hsign, one_mul]
  have h5 : (⟨pinnedX F4.tag Ω (F4.dualRoot α)
        (c ^ F4.exponent (pinnedData F4.tag α).1), pinnedX_mem_adjointGroup _ _⟩ :
            adjointGroup F4.tag Ω) =
      Adjoint.f4Par Ω (F4.dualRoot α) (c ^ F4.exponent (pinnedData F4.tag α).1) := by
    refine Subtype.ext ?_
    rw [CFSG.StandardType.F4ExplicitPos.C3Algebraic.f4Par_coe_eq_pinnedX_alg (K := Ω)
        (ReeTag.isRoot_dualRoot (t := .F4) hα) _,
      pinnedFamilySign_eq_one_charTwo Ω _, one_mul]
    rfl
  exact h2.trans (h3.trans (h4.trans h5))

theorem range_iOmega_eq_C3Levi :
    (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω).range = C3Levi Ω := by
  apply Subgroup.map_injective (f := (adjointGroup .F4 Ω).subtype)
    (adjointGroup .F4 Ω).subtype_injective
  rw [← MonoidHom.range_comp,
    C3Algebraic.range_eq_rootSpan_alg (C3Algebraic.iOmega Ω)
      (fun γ c => CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_x Ω γ c),
    show C3Range.c3RootSet = CFSG.SeitzReduction.F4Pilot.c3LeviRoots from by
      rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet]
      exact CFSG.SeitzReduction.F4Pilot.image_c3ToF4_roots,
    CFSG.SeitzReduction.F4Pilot.map_subtype_C3Levi]

end B3
end CFSG.StandardType.F4ExplicitPos.B3Algebraic
end

end
