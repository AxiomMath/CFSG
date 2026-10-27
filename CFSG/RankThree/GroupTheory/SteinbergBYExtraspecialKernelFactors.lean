module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXExtraspecialOddAction
public import CFSG.LinearAlgebra.SteinbergBQShearGroup
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open Subgroup CFSG.LocalAnalysis.GorensteinLyons CFSG.LinearAlgebra CFSG.LinearAlgebra.SteinbergBQ
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open TauCeti.QuadraticMap (orthogonalGroup)
open scoped commutatorElement

section Lin

open scoped IsMulCommutative

variable {K : Type*} [Group K] [CFSG.IsElementaryAbelian 2 (K ⧸ center K)]

@[expose] noncomputable def subgroupEquiv :
    Subgroup (K ⧸ center K) ≃o Submodule (ZMod 2) (Additive (K ⧸ center K)) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

@[expose] noncomputable def autLin (σ : MulAut K) :
    Additive (K ⧸ center K) ≃ₗ[ZMod 2] Additive (K ⧸ center K) :=
  (MulEquiv.toAdditive (centerQuotientHom K σ)).toLinearEquiv fun c x =>
    ((MulEquiv.toAdditive (centerQuotientHom K σ)).toAddMonoidHom.toZModLinearMap 2).map_smul c x

theorem autLin_apply (σ : MulAut K) (w : Additive (K ⧸ center K)) :
    autLin σ w = Additive.ofMul (centerQuotientHom K σ w.toMul) := rfl

@[expose] noncomputable def autLinHom :
    MulAut K →* (Additive (K ⧸ center K) ≃ₗ[ZMod 2] Additive (K ⧸ center K)) where
  toFun := autLin
  map_one' := LinearEquiv.ext fun w => by
    rw [autLin_apply, map_one]
    rfl
  map_mul' σ τ := LinearEquiv.ext fun w => by
    rw [LinearEquiv.mul_apply, autLin_apply, autLin_apply, autLin_apply, map_mul]
    rfl

variable {z : K}

theorem sqVal_one (H : CommPairHyp K z) (hz : center K = zpowers z) :
    sqVal z (1 : K ⧸ center K) = 0 := by
  rw [← QuotientGroup.mk_one, H.sqVal_mk hz, one_pow, H.zlog_one]

@[expose] noncomputable def sqQuad (H : CommPairHyp K z) (hz : center K = zpowers z) :
    QuadraticForm (ZMod 2) (Additive (K ⧸ center K)) where
  toFun w := sqVal z w.toMul
  toFun_smul a w := by
    have key : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases key a with rfl | rfl
    · rw [zero_smul, toMul_zero, zero_mul, zero_smul, sqVal_one H hz]
    · rw [one_smul, one_mul, one_smul]
  exists_companion' := ⟨H.commForm, fun x y => by
    rw [toMul_add, H.sqVal_mul hz, H.commForm_apply]⟩

theorem sqQuad_apply (H : CommPairHyp K z) (hz : center K = zpowers z)
    (w : Additive (K ⧸ center K)) : sqQuad H hz w = sqVal z w.toMul := rfl

theorem polar_sqQuad (H : CommPairHyp K z) (hz : center K = zpowers z)
    (x y : Additive (K ⧸ center K)) :
    QuadraticMap.polar (sqQuad H hz) x y = commVal z x.toMul y.toMul := by
  rw [QuadraticMap.polar, sqQuad_apply, sqQuad_apply, sqQuad_apply, toMul_add, H.sqVal_mul hz]
  ring

theorem polarBilin_sqQuad_nondegenerate (H : CommPairHyp K z) (hz : center K = zpowers z) :
    (QuadraticMap.polarBilin (sqQuad H hz)).Nondegenerate := by
  have h : QuadraticMap.polarBilin (sqQuad H hz) = H.commForm := by
    ext x y
    rw [QuadraticMap.polarBilin_apply_apply, polar_sqQuad, H.commForm_apply]
  rw [h]
  exact H.commForm_nondegenerate

omit [CFSG.IsElementaryAbelian 2 (K ⧸ center K)] in
theorem sqVal_centerQuotientHom (H : CommPairHyp K z) (hz : center K = zpowers z) (σ : MulAut K)
    (v : K ⧸ center K) : sqVal z (centerQuotientHom K σ v) = sqVal z v := by
  induction v using QuotientGroup.induction_on with | H x =>
  rw [CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk, H.sqVal_mk hz,
    H.sqVal_mk hz, ← map_pow]
  have hx2 : x ^ 2 = 1 ∨ x ^ 2 = z :=
    eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two H.orderOf_eq (hz ▸ H.sq_mem_center x)
  rcases hx2 with h | h <;> rw [h]
  · rw [map_one]
  · rw [mulAut_apply_eq_of_center_eq hz H.orderOf_eq]

theorem autLin_mem_orthogonalGroup (H : CommPairHyp K z) (hz : center K = zpowers z)
    (σ : MulAut K) : autLin σ ∈ orthogonalGroup (sqQuad H hz) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  rw [sqQuad_apply, sqQuad_apply, autLin_apply, toMul_ofMul, sqVal_centerQuotientHom H hz]

end Lin

end CFSG.RankThree.GroupTheory.SteinbergBY
