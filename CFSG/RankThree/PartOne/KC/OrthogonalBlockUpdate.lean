module

public import CFSG.RankThree.PartOne.KC.OrthogonalCentralizerBlocks

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Update

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {x : V ≃ₗ[K] V} (hsq : Squarefree (minpoly K x.toLinearMap))

abbrev BlockGL (x : V ≃ₗ[K] V) (b : K[X]) : Type _ :=
  LinearMap.GeneralLinearGroup (AdjoinRoot b) (primaryComponent x.toLinearMap b)

open scoped _root_.Classical in
@[expose] noncomputable def blockUpdate (a : primaryFactors x.toLinearMap)
    (γ : BlockGL x a) :
    (Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V)) :=
  (theta x hsq).symm (Function.update (1 : (b : primaryFactors x.toLinearMap) → BlockGL x b) a γ)

theorem blockUpdate_apply_self (a : primaryFactors x.toLinearMap)
    (γ : BlockGL x a) (v : primaryComponent x.toLinearMap a) :
    ((blockUpdate hsq a γ).1 (v : V)) = ((γ : Module.End (AdjoinRoot (a : K[X]))
      (primaryComponent x.toLinearMap a)) v : V) := by
  classical
  have h1 := coe_theta_apply x hsq (blockUpdate hsq a γ) a v
  have h2 : theta x hsq (blockUpdate hsq a γ) =
      Function.update (1 : (b : primaryFactors x.toLinearMap) → BlockGL x b) a γ :=
    (theta x hsq).apply_symm_apply _
  rw [← h1, h2]
  simp

theorem blockUpdate_apply_ne (a b : primaryFactors x.toLinearMap) (hab : b ≠ a)
    (γ : BlockGL x a) (v : primaryComponent x.toLinearMap b) :
    ((blockUpdate hsq a γ).1 (v : V)) = v := by
  classical
  have h1 := coe_theta_apply x hsq (blockUpdate hsq a γ) b v
  have h2 : theta x hsq (blockUpdate hsq a γ) =
      Function.update (1 : (b : primaryFactors x.toLinearMap) → BlockGL x b) a γ :=
    (theta x hsq).apply_symm_apply _
  rw [← h1, h2]
  simp [hab]

end Update

end CFSG.RankThree.PartOne.KCOrthogonal
