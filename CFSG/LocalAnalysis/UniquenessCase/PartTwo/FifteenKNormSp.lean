module

public import CFSG.Open.StatedDefs
import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassN
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
import CFSG.ClassicalGroups.Symplectic.Model

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open LinearMap (BilinForm)
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open scoped Matrix

private theorem s15k_norm_sp_alt (m : ℕ) :
    (Matrix.toBilin' (Matrix.J (Fin m) (ZMod 2))).IsAlt := by
  intro v
  rw [Matrix.toBilin'_apply']
  have hv : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := (Sum.elim_comp_inl_inr v).symm
  rw [hv]
  simp [Matrix.J, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec,
    Matrix.one_mulVec]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_comm (v (Sum.inr i)) (v (Sum.inl i))]
  exact CharTwo.add_self_eq_zero _

private theorem s15k_norm_sp_nondeg (m : ℕ) :
    (Matrix.toBilin' (Matrix.J (Fin m) (ZMod 2))).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  intro h0
  have := Matrix.J_det_mul_J_det (Fin m) (ZMod 2)
  rw [h0] at this
  simp at this

private theorem s15k_norm_sp_gram (m : ℕ) :
    LinearMap.BilinForm.toMatrix (Pi.basisFun (ZMod 2) (Fin m ⊕ Fin m))
      (Matrix.toBilin' (Matrix.J (Fin m) (ZMod 2))) = Matrix.J (Fin m) (ZMod 2) := by
  rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']

private theorem s15k_norm_sp_map_eq {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (f : LinearMap.BilinForm (ZMod 2) V) {m : ℕ}
    (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) V)
    (hb : BilinForm.toMatrix b f = Matrix.J (Fin m) (ZMod 2)) :
    (bilinIsometryGroup f).map (mclt_glMatrixEquiv b).toMonoidHom = StatedSp m (ZMod 2) := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
  ext A
  rw [Subgroup.mem_map_equiv]
  have hcoord : ∀ v : V, b.equivFun ((((mclt_glMatrixEquiv b).symm A :
      LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) =
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)).mulVec (b.equivFun v) := by
    intro v
    rw [← mclt_glMatrixEquiv_mulVec, MulEquiv.apply_symm_apply]
  have hmat : LinearMap.toMatrix b b (((mclt_glMatrixEquiv b).symm A :
      LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) =
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) := by
    apply Matrix.mulVec_injective
    funext u
    obtain ⟨v, rfl⟩ := b.equivFun.surjective u
    simp only [Module.Basis.equivFun_apply]
    rw [LinearMap.toMatrix_mulVec_repr]
    simpa only [Module.Basis.equivFun_apply] using hcoord v
  rw [mem_bilinIsometryGroup, ← TauCeti.BilinForm.isIsometry_iff,
    TauCeti.BilinForm.isIsometry_iff_toMatrix b, hmat, hb, TauCeti.GLSymplectic.mem_iff']

theorem s15k_norm_sp_zmod2 (m : ℕ) (M : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) (ZMod 2))
    (hM : ∀ g ∈ StatedSp m (ZMod 2), M * g * M⁻¹ ∈ StatedSp m (ZMod 2)) :
    M ∈ StatedSp m (ZMod 2) := by
  let b := Pi.basisFun (ZMod 2) (Fin m ⊕ Fin m)
  let f : LinearMap.BilinForm (ZMod 2) (Fin m ⊕ Fin m → ZMod 2) :=
    Matrix.toBilin' (Matrix.J (Fin m) (ZMod 2))
  have hb : BilinForm.toMatrix b f = Matrix.J (Fin m) (ZMod 2) := s15k_norm_sp_gram m
  have hmap := s15k_norm_sp_map_eq f b hb
  have key : ∀ N : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) (ZMod 2),
      N ∈ StatedSp m (ZMod 2) ↔ (mclt_glMatrixEquiv b).symm N ∈ bilinIsometryGroup f := by
    intro N
    rw [← hmap, Subgroup.mem_map_equiv]
  rw [key]
  have hg : ∀ x ∈ bilinIsometryGroup f, (mclt_glMatrixEquiv b).symm M * x *
      ((mclt_glMatrixEquiv b).symm M)⁻¹ ∈ bilinIsometryGroup f := by
    intro x hx
    have hx' : mclt_glMatrixEquiv b x ∈ StatedSp m (ZMod 2) := by
      rw [key, MulEquiv.symm_apply_apply]
      exact hx
    have := hM _ hx'
    rw [key] at this
    simpa using this
  exact i28_14_N_sp (s15k_norm_sp_nondeg m) (s15k_norm_sp_alt m) hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
