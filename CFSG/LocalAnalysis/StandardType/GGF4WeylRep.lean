module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LocalAnalysis.StandardType.GGF4WeylMat
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.StandardType.F4Model

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem

noncomputable def rho :
    WeylGroup Tag.F4 →* Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ where
  toFun w := LinearMap.toMatrixAlgEquiv' (weylAction (isFiniteType_cartan Tag.F4) w)
  map_one' := by
    show LinearMap.toMatrixAlgEquiv' (weylAction (isFiniteType_cartan Tag.F4) 1) = 1
    first
    | (rw [map_one]; exact map_one _)
    | (simp; done)
  map_mul' a b := by
    show LinearMap.toMatrixAlgEquiv' (weylAction (isFiniteType_cartan Tag.F4) (a * b)) =
      LinearMap.toMatrixAlgEquiv' (weylAction (isFiniteType_cartan Tag.F4) a) *
        LinearMap.toMatrixAlgEquiv' (weylAction (isFiniteType_cartan Tag.F4) b)
    first
    | (rw [map_mul, map_mul]; done)
    | (simp; done)

theorem rho_injective : Function.Injective rho := by
  intro a b h
  have h' : LinearMap.toMatrixAlgEquiv' (weylAction (isFiniteType_cartan Tag.F4) a) =
      LinearMap.toMatrixAlgEquiv' (weylAction (isFiniteType_cartan Tag.F4) b) := h
  have h1 : weylAction (isFiniteType_cartan Tag.F4) a =
      weylAction (isFiniteType_cartan Tag.F4) b :=
    LinearMap.toMatrixAlgEquiv'.injective h'
  refine ext_single fun i => ?_
  rw [smul_def, smul_def, h1]

theorem cartan_F4_entry (i j : Fin Tag.F4.rank) :
    Tag.F4.cartan i j = (![![2, -1, 0, 0], ![-1, 2, -1, 0], ![0, -2, 2, -1], ![0, 0, -1, 2]] :
      Fin 4 → Fin 4 → ℤ) i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem rho_entry (i a j : Fin 4) :
    ((Pi.single j 1 : Fin 4 → ℤ) - (![![2, -1, 0, 0], ![-1, 2, -1, 0], ![0, -2, 2, -1],
      ![0, 0, -1, 2]] : Fin 4 → Fin 4 → ℤ) i j • (Pi.single i 1 : Fin 4 → ℤ)) a =
      (Sm i).toMat a j := by
  fin_cases i <;> fin_cases a <;> fin_cases j <;>
    first
    | decide
    | (simp [Pi.single_apply, Sm, Sdata, M4.toMat]; done)
    | (simp [Pi.single_apply, Sm, Sdata, M4.toMat]; norm_num; done)

theorem rho_simple (i : Fin Tag.F4.rank) : rho (simple Tag.F4 i) = (Sm i).toMat := by
  ext a j
  have hφ : weylAction (isFiniteType_cartan Tag.F4) (simple Tag.F4 i) =
      reflection Tag.F4.cartan i := weylAction_simple (isFiniteType_cartan Tag.F4) i
  show LinearMap.toMatrixAlgEquiv' (weylAction (isFiniteType_cartan Tag.F4) (simple Tag.F4 i)) a j
    = _
  rw [hφ, LinearMap.toMatrixAlgEquiv'_apply, reflection_apply_coroot, coroot_single,
    cartan_F4_entry]
  first
  | exact rho_entry i a j
  | simpa using rho_entry i a j

theorem coxeterMatrix_F4 : coxeterMatrix (isFiniteType_cartan Tag.F4) = CoxeterMatrix.F₄ := by
  have hC : GGIntCartan CoxeterMatrix.F₄ (Tag.cartan .F4) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  exact coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan Tag.F4) hC

theorem exists_mulEquiv {W : Type} [Group W] (cs : CoxeterSystem CoxeterMatrix.F₄ W) :
    ∃ Φ : W ≃* WeylGroup Tag.F4, ∀ i : Fin 4, Φ (cs.simple i) = simple Tag.F4 i := by
  have key : ∀ (M₁ M₂ : CoxeterMatrix (Fin 4)) (_ : M₁ = M₂),
      ∃ Ψ : M₂.Group ≃* M₁.Group, ∀ i, Ψ (M₂.simple i) = M₁.simple i := by
    intro M₁ M₂ h
    subst h
    exact ⟨MulEquiv.refl _, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ := key _ _ coxeterMatrix_F4
  refine ⟨cs.mulEquiv.trans Ψ, fun i => ?_⟩
  have h1 : cs.mulEquiv (cs.simple i) = CoxeterMatrix.F₄.simple i :=
    cs.mulEquiv.apply_symm_apply _
  show Ψ (cs.mulEquiv (cs.simple i)) = _
  rw [h1]
  exact hΨ i

noncomputable def rho4 : WeylGroup Tag.F4 →* Matrix (Fin 4) (Fin 4) ℤ := rho

theorem rho4_injective : Function.Injective rho4 := rho_injective

theorem rho4_simple (i : Fin 4) : rho4 (simple Tag.F4 i) = (Sm i).toMat := rho_simple i

end CFSG.StandardType.F4Model

end
