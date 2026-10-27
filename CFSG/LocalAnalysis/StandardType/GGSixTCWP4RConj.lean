module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC1
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Orbit

public section

namespace CFSG.StandardType.TableCRes


open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section ConjData

variable {τ : Tag}

@[expose] noncomputable def tcrConjPerm (g : WeylGroup τ) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) :
    Equiv.Perm (Fin τ.rank → ℤ) :=
  (MulAction.toPerm g) * ρ * (MulAction.toPerm g)⁻¹

theorem tcrConjPerm_apply (g : WeylGroup τ) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (x : Fin τ.rank → ℤ) : tcrConjPerm g ρ x = g • ρ (g⁻¹ • x) := by
  unfold tcrConjPerm
  simp [Equiv.Perm.mul_apply, MulAction.toPerm_symm_apply]

private theorem tcrConjPerm_iterate (g : WeylGroup τ) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (s : ℕ)
    (x : Fin τ.rank → ℤ) :
    (⇑(tcrConjPerm g ρ))^[s] x = g • (⇑ρ)^[s] (g⁻¹ • x) := by
  induction s generalizing x with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih, tcrConjPerm_apply, inv_smul_smul,
      Function.iterate_succ_apply']

private theorem tch_iterate_image (g : WeylGroup τ) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (s : ℕ)
    (Ψ : Set (Fin τ.rank → ℤ)) :
    (⇑(tcrConjPerm g ρ))^[s] '' ((fun γ => g • γ) '' Ψ) =
      (fun γ => g • γ) '' ((⇑ρ)^[s] '' Ψ) := by
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  simp only [tcrConjPerm_iterate, inv_smul_smul]

theorem componentOrbitLength_conj (g : WeylGroup τ) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Ψ : Set (Fin τ.rank → ℤ)) :
    componentOrbitLength (tcrConjPerm g ρ) ((fun γ => g • γ) '' Ψ) = componentOrbitLength ρ Ψ := by
  unfold componentOrbitLength
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, tch_iterate_image]
  constructor
  · rintro ⟨hpos, h⟩
    exact ⟨hpos, Set.image_injective.2 (MulAction.injective g) h⟩
  · rintro ⟨hpos, h⟩
    exact ⟨hpos, by rw [h]⟩

private theorem tch_conj_closure_fwd
    (w : WeylGroup τ) (P : Set (Fin τ.rank → ℤ)) (x : WeylGroup τ)
    (hx : x ∈ Subgroup.closure
      {s : WeylGroup τ | ∃ δ ∈ (fun x => w • x) '' P, s = rootReflection δ}) :
    w⁻¹ * x * w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ P, s = rootReflection γ} := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨δ, hδ, rfl⟩ := hy
    obtain ⟨γ, hγP, rfl⟩ := hδ
    have hc : w⁻¹ * rootReflection (w • γ) * w = rootReflection γ := by
      rw [rootReflection_smul_all w γ]
      group
    rw [hc]
    exact Subgroup.subset_closure ⟨γ, hγP, rfl⟩
  | one => simp
  | mul a b ha hb iha ihb =>
    have hc : w⁻¹ * (a * b) * w = (w⁻¹ * a * w) * (w⁻¹ * b * w) := by group
    rw [hc]
    exact mul_mem iha ihb
  | inv a ha iha =>
    have hc : w⁻¹ * a⁻¹ * w = (w⁻¹ * a * w)⁻¹ := by group
    rw [hc]
    exact inv_mem iha

private theorem tch_conj_closure_bwd
    (w : WeylGroup τ) (P : Set (Fin τ.rank → ℤ)) (x : WeylGroup τ)
    (hx : x ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ P, s = rootReflection γ}) :
    w * x * w⁻¹ ∈ Subgroup.closure
      {s : WeylGroup τ | ∃ δ ∈ (fun x => w • x) '' P, s = rootReflection δ} := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨γ, hγP, rfl⟩ := hy
    have hc : w * rootReflection γ * w⁻¹ = rootReflection (w • γ) := by
      rw [rootReflection_smul_all w γ]
    rw [hc]
    exact Subgroup.subset_closure ⟨w • γ, ⟨γ, hγP, rfl⟩, rfl⟩
  | one => simp
  | mul a b ha hb iha ihb =>
    have hc : w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
    rw [hc]
    exact mul_mem iha ihb
  | inv a ha iha =>
    have hc : w * a⁻¹ * w⁻¹ = (w * a * w⁻¹)⁻¹ := by group
    rw [hc]
    exact inv_mem iha

theorem twistInner_conj
    (g : WeylGroup τ) (Ψ : Set (Fin τ.rank → ℤ)) (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) :
    twistInner ((fun x => g • x) '' Ψ) (fun x => g • σ (g⁻¹ • x)) ↔ twistInner Ψ σ := by
  constructor
  · rintro ⟨v, hv, hfix⟩
    refine ⟨g⁻¹ * v * g, tch_conj_closure_fwd g Ψ v hv, fun γ hγ => ?_⟩
    have h1 := hfix (g • γ) ⟨γ, hγ, rfl⟩
    simp only [inv_smul_smul] at h1
    calc σ γ = g⁻¹ • (g • σ γ) := (inv_smul_smul g _).symm
      _ = g⁻¹ • (v • (g • γ)) := by rw [h1]
      _ = (g⁻¹ * v * g) • γ := by rw [← mul_smul, ← mul_smul]
  · rintro ⟨v, hv, hfix⟩
    refine ⟨g * v * g⁻¹, tch_conj_closure_bwd g Ψ v hv, fun γ' hγ' => ?_⟩
    obtain ⟨γ, hγ, rfl⟩ := hγ'
    simp only [inv_smul_smul, mul_smul, hfix γ hγ]

theorem twistKindOf_conj
    (g : WeylGroup τ) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Ψ : Set (Fin τ.rank → ℤ)) :
    twistKindOf (tcrConjPerm g ρ) ((fun γ => g • γ) '' Ψ) = twistKindOf ρ Ψ := by
  have hiter : ∀ n : ℕ, (⇑(tcrConjPerm g ρ))^[n] = fun x => g • (⇑ρ)^[n] (g⁻¹ • x) :=
    fun n => funext fun x => tcrConjPerm_iterate g ρ n x
  unfold twistKindOf
  rw [componentOrbitLength_conj, compRank_image g Ψ,
    Set.ncard_image_of_injective _ (MulAction.injective g), hiter, hiter,
    twistInner_conj g Ψ ((⇑ρ)^[componentOrbitLength ρ Ψ]),
    twistInner_conj g Ψ ((⇑ρ)^[2 * componentOrbitLength ρ Ψ])]

theorem labAt_conj
    (g : WeylGroup τ) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (F : ℕ) (Ψ : Set (Fin τ.rank → ℤ)) :
    LabAt (tcrConjPerm g ρ) F ((fun γ => g • γ) '' Ψ) = LabAt ρ F Ψ := by
  unfold LabAt
  rw [compRank_image g Ψ, Set.ncard_image_of_injective _ (MulAction.injective g),
    twistKindOf_conj g ρ Ψ, componentOrbitLength_conj g ρ Ψ]

end ConjData




open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section CompImage

variable {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']

private theorem tch_eqvGen_map {α β : Type*} {R : α → α → Prop} {R' : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → R' (f x) (f y)) {x y : α} (h : Relation.EqvGen R x y) :
    Relation.EqvGen R' (f x) (f y) := by
  induction h with
  | rel x y h => exact Relation.EqvGen.rel _ _ (hf x y h)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private theorem tch_eqvGen_congr {α : Type*} {R : α → α → Prop} {a a' b b' : α}
    (ha : a = a') (hb : b = b') (h : Relation.EqvGen R a b) : Relation.EqvGen R a' b' := by
  subst ha hb
  exact h

private theorem tch_rel_smul
    (g : WeylGroup τ) (α β : Fin τ.rank → ℤ) :
    dotProduct (g • α) (Matrix.mulVec τ.symmetrizedCartan (g • β)) ≠ 0 ↔
      dotProduct α (Matrix.mulVec τ.symmetrizedCartan β) ≠ 0 := by
  rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform, iform_smul]

private theorem tch_smul_mem_kernelRoots {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (g : WeylGroup τ) (hker : kernelRoots χ' = (fun γ => g • γ) '' kernelRoots χ)
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) : g • α ∈ kernelRoots χ' := by
  rw [hker]
  exact Set.mem_image_of_mem _ hα

private theorem tch_inv_smul_mem_kernelRoots {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (g : WeylGroup τ) (hker : kernelRoots χ' = (fun γ => g • γ) '' kernelRoots χ)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ kernelRoots χ') : g⁻¹ • β ∈ kernelRoots χ := by
  rw [hker] at hβ
  obtain ⟨a, ha, rfl⟩ := hβ
  show g⁻¹ • g • a ∈ kernelRoots χ
  rw [inv_smul_smul]
  exact ha

private theorem tch_eqvGen_smul_fwd
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (g : WeylGroup τ) (hker : kernelRoots χ' = (fun γ => g • γ) '' kernelRoots χ)
    {a b : kernelRoots χ}
    (h : Relation.EqvGen (fun α β : kernelRoots χ =>
      dotProduct (α : Fin τ.rank → ℤ) (Matrix.mulVec τ.symmetrizedCartan (β : Fin τ.rank → ℤ)) ≠ 0)
      a b) :
    Relation.EqvGen (fun α β : kernelRoots χ' =>
      dotProduct (α : Fin τ.rank → ℤ) (Matrix.mulVec τ.symmetrizedCartan (β : Fin τ.rank → ℤ)) ≠ 0)
      ⟨g • (a : Fin τ.rank → ℤ), tch_smul_mem_kernelRoots g hker a.2⟩
      ⟨g • (b : Fin τ.rank → ℤ), tch_smul_mem_kernelRoots g hker b.2⟩ := by
  refine tch_eqvGen_map (fun a : kernelRoots χ =>
    (⟨g • (a : Fin τ.rank → ℤ), tch_smul_mem_kernelRoots g hker a.2⟩ : kernelRoots χ')) ?_ h
  intro x y hxy
  exact (tch_rel_smul g (x : Fin τ.rank → ℤ) (y : Fin τ.rank → ℤ)).2 hxy

private theorem tch_eqvGen_smul_bwd
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (g : WeylGroup τ) (hker : kernelRoots χ' = (fun γ => g • γ) '' kernelRoots χ)
    {a b : kernelRoots χ'}
    (h : Relation.EqvGen (fun α β : kernelRoots χ' =>
      dotProduct (α : Fin τ.rank → ℤ) (Matrix.mulVec τ.symmetrizedCartan (β : Fin τ.rank → ℤ)) ≠ 0)
      a b) :
    Relation.EqvGen (fun α β : kernelRoots χ =>
      dotProduct (α : Fin τ.rank → ℤ) (Matrix.mulVec τ.symmetrizedCartan (β : Fin τ.rank → ℤ)) ≠ 0)
      ⟨g⁻¹ • (a : Fin τ.rank → ℤ), tch_inv_smul_mem_kernelRoots g hker a.2⟩
      ⟨g⁻¹ • (b : Fin τ.rank → ℤ), tch_inv_smul_mem_kernelRoots g hker b.2⟩ := by
  refine tch_eqvGen_map (fun a : kernelRoots χ' =>
    (⟨g⁻¹ • (a : Fin τ.rank → ℤ), tch_inv_smul_mem_kernelRoots g hker a.2⟩ : kernelRoots χ)) ?_ h
  intro x y hxy
  exact (tch_rel_smul g⁻¹ (x : Fin τ.rank → ℤ) (y : Fin τ.rank → ℤ)).2 hxy

theorem exists_componentRoots_image
    (g : WeylGroup τ) {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (hker : kernelRoots χ' = (fun γ => g • γ) '' kernelRoots χ) (i : KernelComponent χ) :
    ∃ i' : KernelComponent χ',
      componentRoots χ' i' = (fun γ => g • γ) '' componentRoots χ i := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep i
  have hgx : g • (x : Fin τ.rank → ℤ) ∈ kernelRoots χ' := tch_smul_mem_kernelRoots g hker x.2
  refine ⟨⟦⟨g • (x : Fin τ.rank → ℤ), hgx⟩⟧, ?_⟩
  ext β'
  constructor
  · rintro ⟨h', hi'⟩
    have hE := tch_eqvGen_smul_bwd (a := (⟨β', h'⟩ : kernelRoots χ'))
      (b := (⟨g • (x : Fin τ.rank → ℤ), hgx⟩ : kernelRoots χ')) g hker (Quotient.exact hi')
    have hx : (⟨g⁻¹ • g • (x : Fin τ.rank → ℤ), tch_inv_smul_mem_kernelRoots g hker hgx⟩ :
        kernelRoots χ) = x :=
      Subtype.ext (inv_smul_smul g _)
    have hq : (⟦⟨g⁻¹ • β', tch_inv_smul_mem_kernelRoots g hker h'⟩⟧ : KernelComponent χ) = ⟦x⟧ :=
      Quotient.sound (tch_eqvGen_congr rfl hx hE)
    exact ⟨g⁻¹ • β', ⟨tch_inv_smul_mem_kernelRoots g hker h', hq⟩, smul_inv_smul g β'⟩
  · rintro ⟨β, ⟨hk, hi⟩, rfl⟩
    exact ⟨tch_smul_mem_kernelRoots g hker hk,
      Quotient.sound (tch_eqvGen_smul_fwd g hker (Quotient.exact hi))⟩

theorem exists_componentRoots_preimage
    (g : WeylGroup τ) {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (hker : kernelRoots χ' = (fun γ => g • γ) '' kernelRoots χ) (i' : KernelComponent χ') :
    ∃ i : KernelComponent χ,
      componentRoots χ' i' = (fun γ => g • γ) '' componentRoots χ i := by
  have hker' : kernelRoots χ = (fun γ => g⁻¹ • γ) '' kernelRoots χ' := by
    ext α
    constructor
    · intro hα
      exact ⟨g • α, tch_smul_mem_kernelRoots g hker hα, inv_smul_smul g α⟩
    · rintro ⟨β, hβ, rfl⟩
      exact tch_inv_smul_mem_kernelRoots g hker hβ
  obtain ⟨i, hi⟩ := exists_componentRoots_image g⁻¹ hker' i'
  refine ⟨i, ?_⟩
  rw [hi, Set.image_image]
  simp only [smul_inv_smul, Set.image_id']

end CompImage

end CFSG.StandardType.TableCRes

end
