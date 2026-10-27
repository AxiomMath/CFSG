module

public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.LocalAnalysis.StandardType.GGLangCoroot
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus Matrix Classical

private abbrev langRatR_rel {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (x y : kernelRoots χ) : Prop :=
  (x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0

private theorem langRatR_eqvGen_map {α β : Type*} {R : α → α → Prop} {R' : β → β → Prop}
    (f : α → β) (hf : ∀ x y, R x y → R' (f x) (f y)) {x y : α}
    (h : Relation.EqvGen R x y) : Relation.EqvGen R' (f x) (f y) := by
  induction h with
  | rel x y h => exact Relation.EqvGen.rel _ _ (hf x y h)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private theorem langRatR_class_eq_of_mem {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i j : KernelComponent χ}
    {α : Fin τ.rank → ℤ} (hi : α ∈ componentRoots χ i) (hj : α ∈ componentRoots χ j) :
    i = j := by
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨hj1, hj2⟩ := hj
  rw [← hi2, ← hj2]

private noncomputable def langRatR_compMap {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (i : KernelComponent χ)
    (hsub : ∀ α : Fin τ.rank → ℤ, α ∈ componentRoots χ i → α ∈ kernelRoots χ')
    (γ₀ : kernelRoots χ') (x : kernelRoots χ) : kernelRoots χ' :=
  if hx : (x : Fin τ.rank → ℤ) ∈ componentRoots χ i then
    ⟨(x : Fin τ.rank → ℤ), hsub (x : Fin τ.rank → ℤ) hx⟩
  else γ₀

private theorem langRatR_compMap_of_mem {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (i : KernelComponent χ)
    (hsub : ∀ α : Fin τ.rank → ℤ, α ∈ componentRoots χ i → α ∈ kernelRoots χ')
    (γ₀ : kernelRoots χ') {x : kernelRoots χ}
    (hx : (x : Fin τ.rank → ℤ) ∈ componentRoots χ i) :
    langRatR_compMap i hsub γ₀ x = ⟨(x : Fin τ.rank → ℤ), hsub (x : Fin τ.rank → ℤ) hx⟩ := by
  simp only [langRatR_compMap, dif_pos hx]

private theorem langRatR_compMap_rel
    {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (i : KernelComponent χ)
    (hsub : ∀ α : Fin τ.rank → ℤ, α ∈ componentRoots χ i → α ∈ kernelRoots χ')
    {γ₀ : kernelRoots χ'} {x y : kernelRoots χ} (h : langRatR_rel χ x y) :
    langRatR_rel χ' (langRatR_compMap i hsub γ₀ x) (langRatR_compMap i hsub γ₀ y) := by
  by_cases hx : (x : Fin τ.rank → ℤ) ∈ componentRoots χ i
  · by_cases hy : (y : Fin τ.rank → ℤ) ∈ componentRoots χ i
    · rw [langRatR_compMap_of_mem i hsub γ₀ hx, langRatR_compMap_of_mem i hsub γ₀ hy]
      exact h
    · exfalso
      have hiform : CFSG.LieType.Steinberg.Adjoint.iform (x : Fin τ.rank → ℤ)
          (y : Fin τ.rank → ℤ) ≠ 0 := by
        rw [← dotProduct_mulVec_eq_iform (x : Fin τ.rank → ℤ) (y : Fin τ.rank → ℤ)]
        exact h
      have hrel : (⟦x⟧ : KernelComponent χ) = ⟦y⟧ := mk_eq_of_iform_ne_zero hiform
      have hxi : (⟦x⟧ : KernelComponent χ) = i := by
        have hxeq : x = ⟨(x : Fin τ.rank → ℤ), hx.1⟩ := Subtype.ext rfl
        rw [hxeq]; exact hx.2
      exact hy ⟨y.2, by rw [← hrel]; exact hxi⟩
  · by_cases hy : (y : Fin τ.rank → ℤ) ∈ componentRoots χ i
    · exfalso
      have hiform : CFSG.LieType.Steinberg.Adjoint.iform (x : Fin τ.rank → ℤ)
          (y : Fin τ.rank → ℤ) ≠ 0 := by
        rw [← dotProduct_mulVec_eq_iform (x : Fin τ.rank → ℤ) (y : Fin τ.rank → ℤ)]
        exact h
      have hrel : (⟦x⟧ : KernelComponent χ) = ⟦y⟧ := mk_eq_of_iform_ne_zero hiform
      have hyi : (⟦y⟧ : KernelComponent χ) = i := by
        have hyeq : y = ⟨(y : Fin τ.rank → ℤ), hy.1⟩ := Subtype.ext rfl
        rw [hyeq]; exact hy.2
      exact hx ⟨x.2, by rw [hrel]; exact hyi⟩
    · have hx' : (langRatR_compMap i hsub γ₀ x : Fin τ.rank → ℤ) =
          (γ₀ : Fin τ.rank → ℤ) := by
        simp only [langRatR_compMap, dif_neg hx]
      have hy' : (langRatR_compMap i hsub γ₀ y : Fin τ.rank → ℤ) =
          (γ₀ : Fin τ.rank → ℤ) := by
        simp only [langRatR_compMap, dif_neg hy]
      show (langRatR_compMap i hsub γ₀ x : Fin τ.rank → ℤ) ⬝ᵥ
        (τ.symmetrizedCartan *ᵥ (langRatR_compMap i hsub γ₀ y : Fin τ.rank → ℤ)) ≠ 0
      rw [hx', hy', dotProduct_mulVec_eq_iform]
      exact ne_of_gt (iform_self_pos_of_isRoot γ₀.2.1)

theorem exists_orbit_of_kills
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a b : Fin τ.rank → Lˣ}
    (ha : rootDiagUnit τ a ∈ S.D.torus) (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hk : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1) :
    ∃ j : KernelComponent (rootCharHom b),
      rationalRoots S.ρ (rootCharHom a) i ⊆ rationalRoots S.ρ (rootCharHom b) j ∧
      componentOrbitLength S.ρ (componentRoots (rootCharHom b) j) ∣
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
        rationalComponent S.ρ S.Γ (rootCharHom b) j := by
  have hsub : ∀ α : Fin τ.rank → ℤ, α ∈ componentRoots (rootCharHom a) i →
      α ∈ kernelRoots (rootCharHom b) := by
    intro α hα
    exact ⟨isRoot_of_mem_rationalRoots S i ⟨0, α, hα, rfl⟩, hk α ⟨0, α, hα, rfl⟩⟩
  obtain ⟨γ₀, hγ₀i⟩ := Quotient.exists_rep i
  have hγ₀Ψ : (γ₀ : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i := ⟨γ₀.2, hγ₀i⟩
  have hγ₀b : (γ₀ : Fin τ.rank → ℤ) ∈ kernelRoots (rootCharHom b) := hsub γ₀ hγ₀Ψ
  have hcomp : componentRoots (rootCharHom a) i ⊆
      componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ := by
    intro α hα
    have hαb : α ∈ kernelRoots (rootCharHom b) := hsub α hα
    refine ⟨hαb, ?_⟩
    have hxi : (⟦⟨α, hα.1⟩⟧ : KernelComponent (rootCharHom a)) = i := hα.2
    have hexp : Relation.EqvGen (langRatR_rel (rootCharHom a)) ⟨α, hα.1⟩ γ₀ :=
      Quotient.exact (hxi.trans hγ₀i.symm)
    have hf : ∀ x y : kernelRoots (rootCharHom a), langRatR_rel (rootCharHom a) x y →
        langRatR_rel (rootCharHom b)
          (langRatR_compMap i hsub ⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩ x)
          (langRatR_compMap i hsub ⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩ y) :=
      fun x y hxy =>
        langRatR_compMap_rel (i := i) (hsub := hsub)
          (γ₀ := ⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩) hxy
    have hmap : Relation.EqvGen (langRatR_rel (rootCharHom b))
        (langRatR_compMap i hsub ⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩ ⟨α, hα.1⟩)
        (langRatR_compMap i hsub ⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩ γ₀) :=
      langRatR_eqvGen_map (fun x => langRatR_compMap i hsub ⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩ x)
        hf hexp
    rw [langRatR_compMap_of_mem i hsub ⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩ hα,
      langRatR_compMap_of_mem i hsub ⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩ hγ₀Ψ] at hmap
    exact Quotient.sound hmap
  have hroots : rationalRoots S.ρ (rootCharHom a) i ⊆
      rationalRoots S.ρ (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ := by
    intro γ hγ
    obtain ⟨k, δ, hδ, rfl⟩ := hγ
    exact ⟨k, δ, hcomp hδ, rfl⟩
  refine ⟨⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧, hroots, ?_, ?_⟩
  ·
    have hsa := outer_componentOrbitLength_spec S ha i
    have hsb := outer_componentOrbitLength_spec S hb ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧
    have hsa_fix : (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)] '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i := hsa.2.1
    have hsb_pos : 0 < componentOrbitLength S.ρ
        (componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧) := hsb.1
    have hsb_fix : (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧)] ''
        componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ =
        componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ := hsb.2.1
    have hsb_min : ∀ k, 0 < k → k < componentOrbitLength S.ρ
        (componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧) →
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k] ''
        componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ ≠
        componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ := hsb.2.2
    obtain ⟨j', hj'⟩ := outer_iterate_image_component S hb
      ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    have hγ_in : (γ₀ : Fin τ.rank → ℤ) ∈ (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)] '' componentRoots (rootCharHom b)
        ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ := by
      have h1 : (γ₀ : Fin τ.rank → ℤ) ∈ (S.ρ : (Fin τ.rank → ℤ) → _)^[
          componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)] ''
          componentRoots (rootCharHom a) i := by
        rw [hsa_fix]; exact hγ₀Ψ
      obtain ⟨δ, hδ, hδγ⟩ := h1
      exact ⟨δ, hcomp hδ, hδγ⟩
    have hmem2 : (γ₀ : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom b) j' := by
      rw [hj']; exact hγ_in
    have hjj' : j' = ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ :=
      langRatR_class_eq_of_mem hmem2 ⟨hγ₀b, rfl⟩
    have hfix_b : (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)] '' componentRoots (rootCharHom b)
        ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ =
        componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ := by
      rw [← hj', hjj']
    have hmod : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) %
        componentOrbitLength S.ρ (componentRoots (rootCharHom b)
          ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧) = 0 := by
      by_contra hne
      have hlt := Nat.mod_lt (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) hsb_pos
      have hper : (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i) % componentOrbitLength S.ρ
          (componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧)] ''
          componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ =
          componentRoots (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ := by
        have h1 := iterate_image_period S hsb_fix
          (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        rw [hfix_b] at h1
        exact h1.symm
      exact hsb_min _ (Nat.pos_of_ne_zero hne) hlt hper
    exact Nat.dvd_of_mod_eq_zero hmod
  ·
    have hspan_le : rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ≤
        rootSpan τ L (rationalRoots S.ρ (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧) :=
      rootSpan_mono hroots
    have hspan : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤
        rationalSpan S.ρ S.Γ (rootCharHom b) ⟦⟨(γ₀ : Fin τ.rank → ℤ), hγ₀b⟩⟧ :=
      inf_le_inf hspan_le le_rfl
    exact Subgroup.commutator_mono hspan hspan

end CFSG.StandardType.LangRat

end
