module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.Fischer.Classification.Orthogonal3.Model
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTransport

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [Module.Finite (ZMod 3) U]
  {A : Subgroup (U ≃ₗ[ZMod 3] U)}

private noncomputable def zct_RL {U : Type} [AddCommGroup U] [Module (ZMod 3) U] {m : ℕ}
    (f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3))
    (L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U) : Set (U ≃ₗ[ZMod 3] U) :=
  {t | ∃ u, f u u = 1 ∧ ∀ x, t (L x) = L (x + f x u • u)}

open Classical in
private noncomputable def zct_reflBarOf {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {m : ℕ} (f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3))
    (L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U) (t : U ≃ₗ[ZMod 3] U) : R3 f :=
  if ht : t ∈ zct_RL f L then reflBar f (Classical.choose ht) else 1

private theorem zct_reflBarOf_mem {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    {L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U} {t : U ≃ₗ[ZMod 3] U}
    (ht : t ∈ zct_RL f L) : zct_reflBarOf f L t ∈ D3 f := by
  rw [zct_reflBarOf, dif_pos ht]
  exact reflBar_mem_D3 (Classical.choose_spec ht).1

private theorem zct_reflBarOf_injOn {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : IsF3Form f) (hm : 4 ≤ m)
    {L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U} :
    Set.InjOn (zct_reflBarOf f L) (zct_RL f L) := by
  intro t₁ ht₁ t₂ ht₂ hbar
  have hs₁ := Classical.choose_spec ht₁
  have hs₂ := Classical.choose_spec ht₂
  have hd : reflBar f (Classical.choose ht₁) = reflBar f (Classical.choose ht₂) := by
    have h₁ : zct_reflBarOf f L t₁ = reflBar f (Classical.choose ht₁) := by
      rw [zct_reflBarOf, dif_pos ht₁]
    have h₂ : zct_reflBarOf f L t₂ = reflBar f (Classical.choose ht₂) := by
      rw [zct_reflBarOf, dif_pos ht₂]
    rw [← h₁, ← h₂]
    exact hbar
  have hgl : F3.refl f (Classical.choose ht₁) = F3.refl f (Classical.choose ht₂) := by
    rcases (reflBar_eq_reflBar_iff hf hm hs₁.1 hs₂.1).mp hd with h' | h'
    · rw [h']
    · rw [h', F3.refl_neg]
  refine LinearEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := L.surjective y
  have hx := congrArg (fun g => F3.act g x) hgl
  rw [F3.act_refl hs₁.1, F3.act_refl hs₂.1] at hx
  rw [hs₁.2 x, hs₂.2 x, hx]

private theorem zct_RL_ncard_le {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : IsF3Form f) (hm : 4 ≤ m)
    {L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U} :
    (zct_RL f L).ncard ≤ (D3 f).ncard :=
  Set.ncard_le_ncard_of_injOn (zct_reflBarOf f L)
    (fun _ ht => zct_reflBarOf_mem ht) (zct_reflBarOf_injOn hf hm)

private theorem zct_RL_finite {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : IsF3Form f) (hm : 4 ≤ m)
    {L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U} : (zct_RL f L).Finite :=
  Set.Finite.of_injOn (fun _ ht => zct_reflBarOf_mem ht) (zct_reflBarOf_injOn hf hm)
    (Set.toFinite _)

theorem isRefl_iff_of_isometry (hn : 3 ≤ Module.finrank (ZMod 3) U) (hirr : AbsIrred 3 A)
    {m : ℕ} (hm : 4 ≤ m) {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 f) (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 f)
    {B : LinearMap.BilinForm (ZMod 3) U}
    (hB : ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u)
    (L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U) (hL : ∀ x y, B (L x) (L y) = f x y)
    (t : U ≃ₗ[ZMod 3] U) :
    (t ∈ A ∧ IsRefl 3 t) ↔ ∃ u, f u u = 1 ∧ ∀ x, t (L x) = L (x + f x u • u) := by
  classical
  let RA : Set (U ≃ₗ[ZMod 3] U) := {t | t ∈ A ∧ IsRefl 3 t}
  have hRA : RA ⊆ zct_RL f L := by
    rintro t ⟨htA, htR⟩
    obtain ⟨u, huu, htu⟩ := hB t htA htR
    refine ⟨L.symm u, ?_, fun x => ?_⟩
    · rw [← hL (L.symm u) (L.symm u), LinearEquiv.apply_symm_apply, huu]
    · rw [htu (L x)]
      have hBx : B (L x) u = f x (L.symm u) := by
        have h := hL x (L.symm u)
        rwa [LinearEquiv.apply_symm_apply] at h
      rw [hBx, map_add, map_smul, LinearEquiv.apply_symm_apply]
  let G : (U ≃ₗ[ZMod 3] U) → (↥A ⧸ Subgroup.center ↥A) := fun t =>
    if ht : t ∈ A then QuotientGroup.mk ⟨t, ht⟩ else 1
  have hGimg : G '' RA = reflImage 3 A := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht.1⟩, ht.2, by simp [G, dif_pos ht.1]⟩
    · rintro ⟨t, htR, rfl⟩
      exact ⟨(t : U ≃ₗ[ZMod 3] U), ⟨t.2, htR⟩, by simp [G, dif_pos t.2]⟩
  have hGinj : Set.InjOn G RA := by
    intro t₁ ht₁ t₂ ht₂ h
    have h' : QuotientGroup.mk (s := Subgroup.center ↥A) (⟨t₁, ht₁.1⟩ : ↥A) =
        QuotientGroup.mk (s := Subgroup.center ↥A) (⟨t₂, ht₂.1⟩ : ↥A) := by
      simpa [G, dif_pos ht₁.1, dif_pos ht₂.1] using h
    exact congrArg Subtype.val (AbsIrred.mk_injOn_refl hirr hn ht₁.2 ht₂.2 h')
  have h2 : (reflImage 3 A).ncard = RA.ncard := by
    rw [← hGimg]
    exact hGinj.ncard_image
  have h3 : (reflImage 3 A).ncard = (D3 f).ncard := by
    rw [← image_eq_of_forall_mem_iff φ hφ]
    exact (Set.ncard_image_of_injective _ φ.injective).symm
  have h4 : (zct_RL f L).ncard ≤ RA.ncard := by
    have := zct_RL_ncard_le hf hm (L := L)
    rwa [← h3, h2] at this
  have hEq : RA = zct_RL f L :=
    Set.eq_of_subset_of_ncard_le hRA h4 (zct_RL_finite hf hm (L := L))
  change t ∈ RA ↔ t ∈ zct_RL f L
  rw [hEq]

end CFSG.StandardType.ZS
