module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.G11.Harris.Sp4

open CFSG.Open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped Matrix

section Form

variable (F : Type) [Field F] [Algebra (ZMod 2) F]

@[expose] noncomputable def symplForm : LinearMap.BilinForm (ZMod 2) (Fin 4 → F) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => Algebra.trace (ZMod 2) F (x ⬝ᵥ (minorJ F *ᵥ y)))
    (fun x x' y => by
      rw [← map_add, add_dotProduct])
    (fun c x y => by
      rw [← map_smul, smul_dotProduct])
    (fun x y y' => by
      rw [← map_add, Matrix.mulVec_add, dotProduct_add])
    (fun c x y => by
      rw [← map_smul, Matrix.mulVec_smul, dotProduct_smul])

theorem symplForm_apply (x y : Fin 4 → F) :
    symplForm F x y = Algebra.trace (ZMod 2) F (x ⬝ᵥ (minorJ F *ᵥ y)) := rfl

variable [Finite F]

private theorem trace_eq_zero_forall {a : F} (h : ∀ b : F, Algebra.trace (ZMod 2) F (a * b) = 0) :
    a = 0 := by
  have hnd := (traceForm_nondegenerate (ZMod 2) F).1
  exact hnd _ fun b => by simpa [Algebra.traceForm_apply] using h b

theorem symplForm_separatingLeft : ∀ x : Fin 4 → F, (∀ y, symplForm F x y = 0) → x = 0 := by
  intro x hx
  funext k
  refine trace_eq_zero_forall F fun b => ?_
  have h := hx (minorJ F *ᵥ Pi.single k b)
  rw [symplForm_apply, Matrix.mulVec_mulVec, minorJ_mul_self, Matrix.one_mulVec] at h
  simpa [dotProduct_single] using h

theorem symplForm_separatingRight : ∀ y : Fin 4 → F, (∀ x, symplForm F x y = 0) → y = 0 := by
  intro y hy
  have h : minorJ F *ᵥ y = 0 := by
    funext k
    refine trace_eq_zero_forall F fun b => ?_
    have h := hy (Pi.single k b)
    rw [symplForm_apply] at h
    simpa [single_dotProduct, mul_comm] using h
  have h2 := congrArg (fun z => minorJ F *ᵥ z) h
  simpa [Matrix.mulVec_mulVec, minorJ_mul_self] using h2

omit [Finite F] in
theorem symplForm_mulVec (N : Matrix (Fin 4) (Fin 4) F) (hN : Nᵀ * minorJ F * N = minorJ F)
    (x y : Fin 4 → F) : symplForm F (N *ᵥ x) (N *ᵥ y) = symplForm F x y := by
  rw [symplForm_apply, symplForm_apply]
  congr 1
  have h1 : ∀ z : Fin 4 → F, (N *ᵥ x) ⬝ᵥ z = x ⬝ᵥ (Nᵀ *ᵥ z) := fun z => by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN]

end Form

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem selfDual_of_symplectic {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {L : Subgroup (GLV V)} (ψ : V ≃ₗ[ZMod 2] (Fin 4 → F)) (N : ↥L → Matrix (Fin 4) (Fin 4) F)
    (hψ : ∀ (h : ↥L) (v : V), ψ ((h : GLV V) v) = N h *ᵥ ψ v)
    (hN : ∀ h, (N h)ᵀ * minorJ F * N h = minorJ F) : CFSG.Quasithin.G11.SelfDual L ⊤ := by
  let e : ↥(⊤ : Submodule (ZMod 2) V) ≃ₗ[ZMod 2] (Fin 4 → F) := Submodule.topEquiv.trans ψ
  refine ⟨(symplForm F).compl₁₂ e.toLinearMap e.toLinearMap, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    apply e.injective
    rw [map_zero]
    apply symplForm_separatingLeft F
    intro y
    simpa using hi (e.symm y)
  · intro j hj
    apply e.injective
    rw [map_zero]
    apply symplForm_separatingRight F
    intro x
    simpa using hj (e.symm x)
  · intro k hk i j i' j' hi hj
    have hki : e i' = N ⟨k, hk⟩ *ᵥ e i := by
      have h := hψ ⟨k, hk⟩ (i : V)
      show ψ (i' : V) = _
      rw [← hi]; exact h
    have hkj : e j' = N ⟨k, hk⟩ *ᵥ e j := by
      have h := hψ ⟨k, hk⟩ (j : V)
      show ψ (j' : V) = _
      rw [← hj]; exact h
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    rw [hki, hkj, symplForm_mulVec F _ (hN ⟨k, hk⟩)]

end CFSG.Quasithin.G11.Harris.Sp4
