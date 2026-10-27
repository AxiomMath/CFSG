module

public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearAut
import CFSG.LieType.SpecialLinear.NormalizerLift.Lift
import CFSG.ClassicalInvolution.WeakCT.AutExtend
import CFSG.ClassicalInvolution.WeakCT.Center
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import Certificates.Certificate113
import CFSG.ClassicalInvolution.WeakCT.StandardPair
import CFSG.ClassicalInvolution.WeakCT.TorusAgree
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient

public section

namespace CFSG.StandardType

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
open CFSG.QuasithinUnique.K1 (stdAut coe_stdAut_zero coe_stdAut_one)

@[expose] noncomputable def ggBlockGL {F : Type} [Field F] (m : ℕ) {k : ℕ} (h : k ≤ m) (A : GL (Fin k) F) :
    GL (Fin m) F :=
  ⟨blockMat m 0 (A : Matrix (Fin k) (Fin k) F),
    blockMat m 0 ((A⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F),
    by rw [← blockMat_mul (by omega), A.mul_inv, blockMat_one],
    by rw [← blockMat_mul (by omega), A.inv_mul, blockMat_one]⟩

theorem ggStdAut_blockSL {F : Type} [Field F] {m k : ℕ} (h : 0 + k ≤ m) (A : GL (Fin k) F) (σ : F ≃+* F)
    {ε : ℕ} (hε : ε ≤ 1) (x : Matrix.SpecialLinearGroup (Fin k) F) :
    stdAut (ggBlockGL m (by omega) A) σ ε (blockSL F m k 0 h x) = blockSL F m k 0 h (stdAut A σ ε x) := by
  have hmap : ∀ X : Matrix (Fin k) (Fin k) F, (blockMat m 0 X).map σ = blockMat m 0 (X.map σ) :=
    fun X => map_blockMat (σ : F →+* F) X
  apply Subtype.ext
  interval_cases ε
  · rw [coe_stdAut_zero, coe_blockSL, coe_blockSL, coe_stdAut_zero, hmap]
    change blockMat m 0 (A : Matrix (Fin k) (Fin k) F) * blockMat m 0 _ *
      blockMat m 0 ((A⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = _
    rw [← blockMat_mul h, ← blockMat_mul h]
  · rw [coe_stdAut_one, ← map_inv, coe_blockSL, coe_blockSL, coe_stdAut_one, transpose_blockMat, hmap]
    change blockMat m 0 (A : Matrix (Fin k) (Fin k) F) * blockMat m 0 _ *
      blockMat m 0 ((A⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = _
    rw [← blockMat_mul h, ← blockMat_mul h]

theorem ggSLChart_exists_align {F : Type} [Field F] [Finite F] {m k : ℕ} (hk : 3 ≤ k) (hkm : k < m)
    {G : Type} [Group G] (ψ₁ : Matrix.SpecialLinearGroup (Fin m) F →* G)
    (h₁ : ψ₁.ker ≤ Subgroup.center _) {g : G}
    (hg : g ∈ Subgroup.normalizer
      (((ψ₁.comp (blockSL F m k 0 (by omega))).range : Subgroup G) : Set G)) :
    ∃ ψ₂ : Matrix.SpecialLinearGroup (Fin m) F →* G, ψ₂.ker ≤ Subgroup.center _ ∧
      ψ₂.range = ψ₁.range.map (MulAut.conj g).toMonoidHom ∧
      ψ₂.comp (blockSL F m k 0 (by omega)) = ψ₁.comp (blockSL F m k 0 (by omega)) := by
  have hker : (ψ₁.comp (blockSL F m k 0 (by omega))).ker ≤
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars k F := by
    intro x hx
    have hx1 : x = 1 := eq_one_of_blockSL_mem_center (by omega) hkm (h₁ hx)
    rw [hx1]
    exact one_mem _
  obtain ⟨A, σ, ε, hε, hconj⟩ := CFSG.LieType.SpecialLinear.exists_stdAut
    (ψ₁.comp (blockSL F m k 0 (by omega))) hker hk ⟨g, hg⟩
  set β := stdAut (ggBlockGL m (by omega) A) σ ε with hβdef
  have hβ : ∀ x, β (blockSL F m k 0 (by omega) x) = blockSL F m k 0 (by omega) (stdAut A σ ε x) :=
    fun x => ggStdAut_blockSL (by omega) A σ hε x
  refine ⟨(MulAut.conj g).toMonoidHom.comp (ψ₁.comp β.symm.toMonoidHom), ?_, ?_, ?_⟩
  · intro y hy
    have hy2 : g * ψ₁ (β.symm y) * g⁻¹ = 1 := hy
    have hc := h₁ (conj_eq_one_iff.mp hy2 : β.symm y ∈ ψ₁.ker)
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have h2 := congrArg β (Subgroup.mem_center_iff.mp hc (β.symm z))
    simpa using h2
  · rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr β.symm.surjective,
      ← MonoidHom.range_eq_map]
  · refine MonoidHom.ext fun x => ?_
    have hs : β.symm (blockSL F m k 0 (by omega) x) =
        blockSL F m k 0 (by omega) ((stdAut A σ ε).symm x) := by
      apply β.injective
      rw [MulEquiv.apply_symm_apply, hβ, MulEquiv.apply_symm_apply]
    have hc := hconj ((stdAut A σ ε).symm x)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs]
    simpa using hc

end CFSG.StandardType

end
