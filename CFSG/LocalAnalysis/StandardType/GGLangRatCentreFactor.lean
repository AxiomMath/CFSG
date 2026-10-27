module

public import CFSG.LocalAnalysis.StandardType.GGLangRatCentreStmts
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open scoped TensorProduct

private theorem langRatCF_rootChar_mul {τ : Tag} {K : Type} [Field K]
    (a b : Fin τ.rank → Kˣ) (δ : Fin τ.rank → ℤ) :
    rootChar (a * b) δ = rootChar a δ * rootChar b δ := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private theorem langRatCF_rootChar_Hchar
    {τ : Tag} {L : Type} [Field L] (x v : Fin τ.rank → ℤ) (u : Lˣ) :
    rootChar (Hchar x u) v = u ^ iform x v := by
  have hsum : iform x v = ∑ l, v l * iform x (Pi.single l 1) := by
    rw [iform_comm x v, CFSG.LieType.Chevalley.iform_eq_sum_single v x]
    exact Finset.sum_congr rfl fun l _ => by rw [iform_comm (Pi.single l 1) x]
  rw [hsum]
  simp only [rootChar, Hchar, ← zpow_mul]
  rw [← Finset.prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun l _ => by rw [mul_comm]

private noncomputable def langRatCF_psi
    {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L] (δ : Fin τ.rank → ℤ) :=
  TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun (x : ↥(Submodule.span ℤ Ψ)) (v : Additive Lˣ) =>
      iform (x : Fin τ.rank → ℤ) δ • v)
    (fun x y v => by rw [Submodule.coe_add, iform_add_left, add_zsmul])
    (fun c x v => by rw [Submodule.coe_smul, iform_smul_left, mul_smul])
    (fun x v w => by rw [zsmul_add])
    (fun c x v => by rw [smul_comm]))

private theorem langRatCF_psi_tmul
    {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L] (δ : Fin τ.rank → ℤ)
    (x : ↥(Submodule.span ℤ Ψ)) (v : Additive Lˣ) :
    langRatCF_psi Ψ L δ (x ⊗ₜ[ℤ] v) = iform (x : Fin τ.rank → ℤ) δ • v := by
  rw [langRatCF_psi, TensorProduct.lift.tmul]
  rfl

private theorem langRatCF_psi_toMul
    {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L] (δ : Fin τ.rank → ℤ)
    (z : TSc Ψ L) :
    Additive.toMul (langRatCF_psi Ψ L δ z) =
      rootChar (Additive.toMul (langRatPiT Ψ L z)) δ := by
  have htmul : ∀ (x : ↥(Submodule.span ℤ Ψ)) (v : Additive Lˣ),
      Additive.toMul (langRatCF_psi Ψ L δ (x ⊗ₜ[ℤ] v)) =
        rootChar (Additive.toMul (langRatPiT Ψ L (x ⊗ₜ[ℤ] v))) δ := by
    intro x v
    rw [langRatCF_psi_tmul, toMul_langRatPiT_tmul]
    change Additive.toMul (iform (x : Fin τ.rank → ℤ) δ • v) =
      rootChar (Hchar (x : Fin τ.rank → ℤ) (Additive.toMul v)) δ
    rw [langRatCF_rootChar_Hchar]
    rfl
  refine TensorProduct.induction_on (motive := fun z =>
      Additive.toMul (langRatCF_psi Ψ L δ z) =
        rootChar (Additive.toMul (langRatPiT Ψ L z)) δ) z ?_ htmul ?_
  · simpa only [TensorProduct.zero_tmul] using htmul 0 0
  · intro z1 z2 h1 h2
    rw [map_add (langRatCF_psi Ψ L δ) z1 z2, map_add (langRatPiT Ψ L) z1 z2]
    change Additive.toMul (langRatCF_psi Ψ L δ z1) * Additive.toMul (langRatCF_psi Ψ L δ z2) =
      rootChar (Additive.toMul (langRatPiT Ψ L z1) * Additive.toMul (langRatPiT Ψ L z2)) δ
    rw [langRatCF_rootChar_mul, h1, h2]

private theorem langRatCF_psi_eq_zero
    {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L] {δ : Fin τ.rank → ℤ}
    (hδ : δ ∈ Ψ) {z : TSc Ψ L}
    (hz : ∀ γ ∈ Ψ, rootChar (Additive.toMul (langRatPiT Ψ L z)) γ = 1) :
    langRatCF_psi Ψ L δ z = 0 := by
  have h := langRatCF_psi_toMul Ψ L δ z
  rw [hz δ hδ] at h
  exact Additive.toMul.injective (by rw [h]; rfl)

private noncomputable def langRatCF_vΛ {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ))
    (v : Fin τ.rank → ℤ) : ↥(Submodule.span ℤ Ψ) := by
  classical
  exact if hv : v ∈ Submodule.span ℤ Ψ then ⟨v, hv⟩ else 0

private theorem langRatCF_vΛ_coe {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ))
    {v : Fin τ.rank → ℤ} (hv : v ∈ Submodule.span ℤ Ψ) :
    ((langRatCF_vΛ Ψ v : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) = v := by
  rw [langRatCF_vΛ, dif_pos hv]

private theorem langRatCF_list_sum_tmul {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ))
    (L : Type) [Field L] (l : List (↥(Submodule.span ℤ Ψ))) (v : Additive Lˣ) :
    (l.sum ⊗ₜ[ℤ] v) = (l.map (fun x => x ⊗ₜ[ℤ] v)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.sum_cons, TensorProduct.add_tmul, ih]

private theorem langRatCF_list_sum_map_zero {β M : Type*} [AddCommMonoid M] (l : List β) :
    (l.map fun _ => (0 : M)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.map_cons, List.sum_cons, ih]

private theorem langRatCF_hx {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ))
    (g : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (h : ↥(Submodule.span ℤ Ψ) →ₗ[ℤ] ↥(Submodule.span ℤ Ψ))
    (l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)))
    (hl : ∀ p ∈ l, p.1 ∈ Ψ ∧ p.2 ∈ Submodule.span ℤ Ψ)
    (hg : ∀ x ∈ Submodule.span ℤ Ψ, g x = (l.map fun p => iform x p.1 • p.2).sum)
    (hx : ∀ x : ↥(Submodule.span ℤ Ψ),
      ((h x : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) = g x)
    (x : ↥(Submodule.span ℤ Ψ)) :
    h x = (l.map fun p => iform (x : Fin τ.rank → ℤ) p.1 • langRatCF_vΛ Ψ p.2).sum := by
  apply Subtype.ext
  rw [hx x, hg x x.2]
  change (List.map (fun p => iform (x : Fin τ.rank → ℤ) p.1 • p.2) l).sum =
    ({ toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      ↥(Submodule.span ℤ Ψ) →+ (Fin τ.rank → ℤ))
      ((List.map (fun p => iform (x : Fin τ.rank → ℤ) p.1 • langRatCF_vΛ Ψ p.2) l).sum)
  rw [← List.sum_map_hom l
    (fun p => iform (x : Fin τ.rank → ℤ) p.1 • langRatCF_vΛ Ψ p.2)
    ({ toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      ↥(Submodule.span ℤ Ψ) →+ (Fin τ.rank → ℤ))]
  exact congrArg List.sum (List.map_congr_left fun p hp => by
    change iform (x : Fin τ.rank → ℤ) p.1 • p.2 =
      ((iform (x : Fin τ.rank → ℤ) p.1 • langRatCF_vΛ Ψ p.2 :
        ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
    rw [Submodule.coe_smul, langRatCF_vΛ_coe Ψ (hl p hp).2])

private theorem langRatCF_smul_tmul_eq {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L]
    (c : ℤ) (u : ↥(Submodule.span ℤ Ψ)) (v : Additive Lˣ) :
    (c • u) ⊗ₜ[ℤ] v = u ⊗ₜ[ℤ] (c • v) := by
  calc (c • u) ⊗ₜ[ℤ] v = c • (u ⊗ₜ[ℤ] v) := (TensorProduct.smul_tmul' c u v).symm
    _ = u ⊗ₜ[ℤ] (c • v) := (TensorProduct.tmul_smul c u v).symm

private theorem langRatCF_map_eq
    {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L]
    (g : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (h : ↥(Submodule.span ℤ Ψ) →ₗ[ℤ] ↥(Submodule.span ℤ Ψ))
    (l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)))
    (hl : ∀ p ∈ l, p.1 ∈ Ψ ∧ p.2 ∈ Submodule.span ℤ Ψ)
    (hg : ∀ x ∈ Submodule.span ℤ Ψ, g x = (l.map fun p => iform x p.1 • p.2).sum)
    (hx : ∀ x : ↥(Submodule.span ℤ Ψ),
      ((h x : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) = g x)
    (z : TSc Ψ L) :
    TensorProduct.map h (LinearMap.id : Additive Lˣ →ₗ[ℤ] Additive Lˣ) z =
      (l.map fun p => langRatCF_vΛ Ψ p.2 ⊗ₜ[ℤ] langRatCF_psi Ψ L p.1 z).sum := by
  have htmul : ∀ (x : ↥(Submodule.span ℤ Ψ)) (v : Additive Lˣ),
      TensorProduct.map h (LinearMap.id : Additive Lˣ →ₗ[ℤ] Additive Lˣ) (x ⊗ₜ[ℤ] v) =
        (l.map fun p =>
          langRatCF_vΛ Ψ p.2 ⊗ₜ[ℤ] langRatCF_psi Ψ L p.1 (x ⊗ₜ[ℤ] v)).sum := by
    intro x v
    rw [TensorProduct.map_tmul, langRatCF_hx Ψ g h l hl hg hx x]
    have hR : (l.map fun p =>
          langRatCF_vΛ Ψ p.2 ⊗ₜ[ℤ] langRatCF_psi Ψ L p.1 (x ⊗ₜ[ℤ] v)) =
        (l.map fun p =>
          langRatCF_vΛ Ψ p.2 ⊗ₜ[ℤ] (iform (x : Fin τ.rank → ℤ) p.1 • v)) := by
      apply List.map_congr_left
      intro p _
      rw [langRatCF_psi_tmul]
    rw [hR, langRatCF_list_sum_tmul, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun (p : _ × _) _ =>
      langRatCF_smul_tmul_eq Ψ L (iform (x : Fin τ.rank → ℤ) p.1) (langRatCF_vΛ Ψ p.2) v)
  refine TensorProduct.induction_on (motive := fun z =>
      TensorProduct.map h (LinearMap.id : Additive Lˣ →ₗ[ℤ] Additive Lˣ) z =
        (l.map fun p => langRatCF_vΛ Ψ p.2 ⊗ₜ[ℤ] langRatCF_psi Ψ L p.1 z).sum)
    z ?_ htmul ?_
  · simpa only [TensorProduct.zero_tmul] using htmul 0 0
  · intro z1 z2 h1 h2
    rw [map_add, h1, h2]
    simp only [map_add, TensorProduct.tmul_add, List.sum_map_add]

theorem langRatCentreOfFactor_holds :
    ∀ (τ : Tag) (L : Type) [Field L] (Ψ : Set (Fin τ.rank → ℤ))
      (g : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (h : ↥(Submodule.span ℤ Ψ) →ₗ[ℤ] ↥(Submodule.span ℤ Ψ)),
      LangRatRootFactor Ψ g →
      (∀ x : ↥(Submodule.span ℤ Ψ), ((h x : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) = g x) →
      ∀ z : TSc Ψ L, (∀ γ ∈ Ψ, rootChar (Additive.toMul (langRatPiT Ψ L z)) γ = 1) →
        TensorProduct.map h (LinearMap.id : Additive Lˣ →ₗ[ℤ] Additive Lˣ) z = 0 := by
  intro τ L _ Ψ g h hfac hagree z hz
  obtain ⟨l, hl, hg⟩ := hfac
  have hstep := langRatCF_map_eq Ψ L g h l hl hg hagree z
  rw [hstep]
  have hmap : (l.map fun p =>
        langRatCF_vΛ Ψ p.2 ⊗ₜ[ℤ] langRatCF_psi Ψ L p.1 z) =
      l.map (fun _ => (0 : ↥(Submodule.span ℤ Ψ) ⊗[ℤ] Additive Lˣ)) := by
    apply List.map_congr_left
    intro p hp
    rw [langRatCF_psi_eq_zero Ψ L (hl p hp).1 hz, TensorProduct.tmul_zero]
  rw [hmap, langRatCF_list_sum_map_zero]

end CFSG.StandardType.LangRat
