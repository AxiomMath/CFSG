module

public import CFSG.RankThree.GF2n.Smith81.OrthE1KF3p
public import CFSG.RankThree.GF2n.Smith81.OrthE1KF9
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFSmall
public import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbOmegaComm
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamilies
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicProof
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
public import CFSG.Sporadic.Bridge.Catalogue
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1001Base
public import Certificates.Certificate10027
public import Certificates.Certificate1004
public import Certificates.Certificate1006
public import Certificates.Certificate1007
public import Certificates.Certificate1007Base
public import Certificates.Certificate1008
public import Certificates.Certificate1010
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate1011
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate1013
public import Certificates.Certificate1014
public import Certificates.Certificate1014Base
public import Certificates.Certificate1015
public import Certificates.Certificate1017
public import Certificates.Certificate1018
public import Certificates.Certificate1018Base
public import Certificates.Certificate1019
public import Certificates.Certificate16018
public import Certificates.Certificate2160
public import Certificates.Certificate2207
public import Certificates.Certificate2246
public import Certificates.Certificate2293
public import Certificates.Certificate2294
public import Certificates.Certificate2304
public import Certificates.Certificate2305
public import Certificates.Certificate2308
public import Certificates.Certificate3037
public import Certificates.Certificate3037Base
public import Certificates.Certificate3038
public import Certificates.Certificate3038Base
public import Certificates.Certificate3148
public import Certificates.Certificate3148Base
public import Certificates.Certificate3150
public import Certificates.Certificate3150Base
public import Certificates.Certificate3151
public import Certificates.Certificate3151Base
public import Certificates.Certificate3152
public import Certificates.Certificate3152Base
public import Certificates.Certificate3153
public import Certificates.Certificate3153Base
public import Certificates.Certificate3154
public import Certificates.Certificate3154Base
public import Certificates.Certificate6006
public import Certificates.Certificate9124

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Rank

theorem rank_vecMulVec_eq_one_KF {ι κ K : Type} [Field K] [Fintype ι] [Fintype κ]
    (w : ι → K) (v : κ → K) (i : ι) (j : κ) (hij : w i * v j ≠ 0) :
    (Matrix.vecMulVec w v).rank = 1 := by
  refine le_antisymm (Matrix.rank_vecMulVec_le w v) ?_
  have hdet : ((Matrix.vecMulVec w v).submatrix (fun _ : Fin 1 => i)
      (fun _ : Fin 1 => j)).det ≠ 0 := by
    rw [Matrix.det_unique]
    simpa [Matrix.vecMulVec_apply] using hij
  have h := Matrix.rank_submatrix_le (Matrix.vecMulVec w v) (fun _ : Fin 1 => i)
    (fun _ : Fin 1 => j)
  rw [Matrix.rank_of_isUnit _ (Matrix.isUnit_iff_isUnit_det _ |>.mpr
    (isUnit_iff_ne_zero.mpr hdet))] at h
  simpa using h

theorem one_add_vecMulVec_sq_KF {ι K : Type} [Field K] [Fintype ι] [DecidableEq ι] (w φ : ι → K)
    (h2 : (2 : K) = 0) (h : φ ⬝ᵥ w = 0) :
    (1 + Matrix.vecMulVec w φ) * (1 + Matrix.vecMulVec w φ) = 1 := by
  have hNN : Matrix.vecMulVec w φ * Matrix.vecMulVec w φ = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, h, zero_smul]
    ext i j
    simp
  have hsum : Matrix.vecMulVec w φ + Matrix.vecMulVec w φ = 0 := by
    rw [← two_smul K, h2, zero_smul]
  calc (1 + Matrix.vecMulVec w φ) * (1 + Matrix.vecMulVec w φ)
      = 1 + (Matrix.vecMulVec w φ + Matrix.vecMulVec w φ)
          + Matrix.vecMulVec w φ * Matrix.vecMulVec w φ := by noncomm_ring
    _ = 1 := by rw [hsum, hNN, add_zero, add_zero]

theorem vecMulVec_mulVec_KF {ι K : Type} [CommRing K] [Fintype ι] (w φ v : ι → K) :
    Matrix.vecMulVec w φ *ᵥ v = (φ ⬝ᵥ v) • w := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

end Rank

section Minus

variable {K : Type} [Field K]

@[expose] def minusVecKF (K : Type) [Field K] : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inr (Sum.inl mIxKF3p)) 1 + Pi.single (Sum.inr (Sum.inr 0)) 1

@[expose] def minusFunKF (K : Type) [Field K] (b : K) : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inl mIxKF3p) 1 + Pi.single (Sum.inr (Sum.inr 1)) b

lemma minusVecKF_quad (b c : K) : StatedQuadMinus 2 K b c (minusVecKF K) = 1 := by
  rw [quad_minus_eq]
  simp [minusVecKF, Pi.single_apply]

lemma minusForm_minusVecKF (b : K) (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :
    minusFormKF3p b v (minusVecKF K) = minusFunKF K b ⬝ᵥ v := by
  simp [minusFormKF3p, minusVecKF, minusFunKF, Pi.single_apply, add_dotProduct] <;> ring

lemma minusFunKF_dot_minusVecKF (b : K) : minusFunKF K b ⬝ᵥ minusVecKF K = 0 := by
  simp [minusFunKF, minusVecKF, Pi.single_apply, add_dotProduct]

theorem minus_transv_isometry [CharP K 2] (b c : K)
    (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus 2 K b c ((1 + Matrix.vecMulVec (minusVecKF K) (minusFunKF K b)) *ᵥ v) =
      StatedQuadMinus 2 K b c v := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  rw [Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec_KF, quad_add_smul_KF3p,
    minusVecKF_quad, minusForm_minusVecKF]
  generalize minusFunKF K b ⬝ᵥ v = s
  linear_combination (s ^ 2) * h2

lemma minusFunKF_coord (b : K) : minusFunKF K b (Sum.inl mIxKF3p) = 1 := by
  simp [minusFunKF, Pi.single_apply]

lemma minusVecKF_coord : minusVecKF K (Sum.inr (Sum.inl mIxKF3p)) = 1 := by
  simp [minusVecKF, Pi.single_apply]

end Minus

section PlusTransv

variable {K : Type} [Field K]

@[expose] def plusVecKF (K : Type) [Field K] : Fin 2 ⊕ Fin 2 → K :=
  Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1

lemma plusVecKF_dot (v : Fin 2 ⊕ Fin 2 → K) :
    plusVecKF K ⬝ᵥ v = v (Sum.inl 0) + v (Sum.inr 0) := by
  simp [plusVecKF, add_dotProduct]

lemma plusVecKF_inl0 : plusVecKF K (Sum.inl 0) = 1 := by
  simp [plusVecKF, Pi.single_apply]

lemma plusVecKF_inr0 : plusVecKF K (Sum.inr 0) = 1 := by
  simp [plusVecKF, Pi.single_apply]

lemma plusVecKF_inl1 : plusVecKF K (Sum.inl 1) = 0 := by
  simp [plusVecKF, Pi.single_apply]

lemma plusVecKF_inr1 : plusVecKF K (Sum.inr 1) = 0 := by
  simp [plusVecKF, Pi.single_apply]

lemma plus_quad_eq (z : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K z = z (Sum.inl 0) * z (Sum.inr 0) + z (Sum.inl 1) * z (Sum.inr 1) := by
  unfold StatedQuadPlus
  simp [CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two]

theorem plus_transv_isometry [CharP K 2] (v : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K ((1 + Matrix.vecMulVec (plusVecKF K) (plusVecKF K)) *ᵥ v) =
      StatedQuadPlus 2 K v := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  rw [Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec_KF, plusVecKF_dot,
    plus_quad_eq, plus_quad_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, plusVecKF_inl0, plusVecKF_inr0,
    plusVecKF_inl1, plusVecKF_inr1, mul_one, mul_zero, add_zero]
  linear_combination ((v (Sum.inl 0) + v (Sum.inr 0)) ^ 2) * h2

end PlusTransv

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def transLinKF : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun X := Xᵀ
  map_add' X Y := Matrix.transpose_add X Y
  map_smul' c X := Matrix.transpose_smul c X

@[expose] def tauLinKF : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
  (pEquivKF3p (K := K)).symm.toLinearMap ∘ₗ transLinKF ∘ₗ (pEquivKF3p (K := K)).toLinearMap

lemma tauLinKF_apply (v : Fin 2 ⊕ Fin 2 → K) : tauLinKF v = vmKF3p ((pmKF3p v)ᵀ) := rfl

lemma tauLinKF_tauLinKF (v : Fin 2 ⊕ Fin 2 → K) : tauLinKF (tauLinKF v) = v := by
  rw [tauLinKF_apply, tauLinKF_apply, pm_vm_KF3p, Matrix.transpose_transpose, vm_pm_KF3p]

lemma tauLinKF_mul_self : tauLinKF * tauLinKF = (1 : Module.End K (Fin 2 ⊕ Fin 2 → K)) :=
  LinearMap.ext fun v => tauLinKF_tauLinKF v

@[expose] def tauGLKF : GL (Fin 2 ⊕ Fin 2) K where
  val := LinearMap.toMatrix' tauLinKF
  inv := LinearMap.toMatrix' tauLinKF
  val_inv := by
    rw [← LinearMap.toMatrix'_mul, tauLinKF_mul_self, LinearMap.toMatrix'_one]
  inv_val := by
    rw [← LinearMap.toMatrix'_mul, tauLinKF_mul_self, LinearMap.toMatrix'_one]

lemma tauGLKF_mul_self : tauGLKF * tauGLKF = (1 : GL (Fin 2 ⊕ Fin 2) K) := by
  apply Units.ext
  show LinearMap.toMatrix' tauLinKF * LinearMap.toMatrix' tauLinKF = 1
  rw [← LinearMap.toMatrix'_mul, tauLinKF_mul_self, LinearMap.toMatrix'_one]

lemma tauGLKF_mulVec (v : Fin 2 ⊕ Fin 2 → K) :
    (tauGLKF (K := K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = tauLinKF v := by
  show LinearMap.toMatrix' tauLinKF *ᵥ v = _
  rw [LinearMap.toMatrix'_mulVec]

lemma GL_eq_of_mulVec_KF {g h : GL (Fin 2 ⊕ Fin 2) K}
    (H : ∀ v : Fin 2 ⊕ Fin 2 → K,
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
        (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) : g = h := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact H v

lemma GL_mulVec_mul_KF (g h : GL (Fin 2 ⊕ Fin 2) K) (v : Fin 2 ⊕ Fin 2 → K) :
    ((g * h : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        ((h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

@[expose] def sltrKF (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨(A : Matrix (Fin 2) (Fin 2) K)ᵀ, by rw [Matrix.det_transpose]; exact A.2⟩

lemma sltrKF_coe (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((sltrKF A : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K)ᵀ := rfl

theorem tau_lm_tau (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    tauGLKF * rhoLKF3p A * tauGLKF⁻¹ = rhoRKF3p (sltrKF A)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right tauGLKF_mul_self]
  apply GL_eq_of_mulVec_KF
  intro v
  simp only [GL_mulVec_mul_KF, tauGLKF_mulVec, rhoLKF3p_apply, rhoRKF3p_apply, inv_inv]
  simp only [tauLinKF_apply, lmKF3p_apply, rmKF3p_apply, pm_vm_KF3p, sltrKF_coe,
    Matrix.transpose_mul, Matrix.transpose_transpose]

theorem tau_rm_tau (C : Matrix.SpecialLinearGroup (Fin 2) K) :
    tauGLKF * rhoRKF3p C * tauGLKF⁻¹ = rhoLKF3p (sltrKF C⁻¹) := by
  rw [inv_eq_of_mul_eq_one_right tauGLKF_mul_self]
  apply GL_eq_of_mulVec_KF
  intro v
  simp only [GL_mulVec_mul_KF, tauGLKF_mulVec, rhoLKF3p_apply, rhoRKF3p_apply]
  simp only [tauLinKF_apply, lmKF3p_apply, rmKF3p_apply, pm_vm_KF3p, sltrKF_coe,
    Matrix.transpose_mul, Matrix.transpose_transpose]

lemma tauGLKF_mem_isometry :
    tauGLKF (K := K) ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K) := by
  refine Subgroup.subset_closure fun v => ?_
  rw [tauGLKF_mulVec, tauLinKF_apply, statedQuadPlus_eq_det, statedQuadPlus_eq_det,
    pm_vm_KF3p, Matrix.det_transpose]

@[expose] def tauVecKF (K : Type) [Field K] : Fin 2 ⊕ Fin 2 → K :=
  Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1

lemma tauGLKF_sub_one_rank :
    Matrix.rank ((tauGLKF (K := K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1) = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hneg : (-1 : K) = 1 := by linear_combination (-1 : K) * h2
  have e : (LinearMap.toMatrix' (tauLinKF (K := K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      - 1 = Matrix.vecMulVec (tauVecKF K) (tauVecKF K) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, tauLinKF_apply, pmKF3p, vmKF3p, tauVecKF,
        Pi.single_apply, Matrix.one_apply, Matrix.vecMulVec_apply, hneg]
  change Matrix.rank ((LinearMap.toMatrix' (tauLinKF (K := K)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1) = 1
  rw [e]
  exact rank_vecMulVec_eq_one_KF _ _ (Sum.inl 1) (Sum.inl 1)
    (by simp [tauVecKF, Pi.single_apply])

lemma tauGLKF_not_mem_omega (h4 : 4 ≤ Nat.card K) :
    tauGLKF (K := K) ∉ StatedOmega (StatedQuadPlus 2 K) := by
  intro hτ
  have hv : ∀ v : Fin 2 ⊕ Fin 2 → K,
      StatedQuadPlus 2 K ((tauGLKF (K := K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        StatedQuadPlus 2 K v := by
    intro v
    rw [tauGLKF_mulVec, tauLinKF_apply, statedQuadPlus_eq_det, statedQuadPlus_eq_det,
      pm_vm_KF3p, Matrix.det_transpose]
  have hD := ((dicksonNat_holds K h4).1 tauGLKF hv tauGLKF_mul_self).mp hτ
  rw [tauGLKF_sub_one_rank] at hD
  exact Nat.not_even_one hD

lemma rhoL_uUp_one_ne : rhoLKF3p (uUpKF3p (1 : K)) ≠ 1 := by
  intro h
  have h' : uUpKF3p (1 : K) = 1 := rhoLKF3p_injective (h.trans (map_one _).symm)
  exact one_ne_zero (uUp_eq_one h')

lemma rhoR_uUp_one_ne : rhoRKF3p (uUpKF3p (1 : K)) ≠ 1 := by
  intro h
  have h' : uUpKF3p (1 : K) = 1 := rhoRKF3p_injective (h.trans (map_one _).symm)
  exact one_ne_zero (uUp_eq_one h')

theorem plus_sup_decomp (h4 : 4 ≤ Nat.card K) {g : GL (Fin 2 ⊕ Fin 2) K}
    (hg : g ∈ StatedOmega (StatedQuadPlus 2 K)) :
    ∃ x ∈ factorOneKF3p (K := K), ∃ y ∈ factorTwoKF3p (K := K), g = x * y := by
  rw [← range_psi_eq_omega h4] at hg
  obtain ⟨⟨A, C⟩, rfl⟩ := hg
  refine ⟨rhoLKF3p A, ⟨A, rfl⟩, rhoRKF3p C, ⟨C, rfl⟩, ?_⟩
  rw [psiKF3p_apply]
  exact (rho_commute A C).symm

theorem factorOne_isSimple (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup ↥(factorOneKF3p (K := K)) := by
  have e : ↥(factorOneKF3p (K := K)) ≃* ↥(StatedSL 2 K) :=
    (MonoidHom.ofInjective rhoLKF3p_injective).symm.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
  exact (MulEquiv.isSimpleGroup_congr e).mpr
    (CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4)

theorem factorTwo_isSimple (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup ↥(factorTwoKF3p (K := K)) := by
  have e : ↥(factorTwoKF3p (K := K)) ≃* ↥(StatedSL 2 K) :=
    (MonoidHom.ofInjective rhoRKF3p_injective).symm.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
  exact (MulEquiv.isSimpleGroup_congr e).mpr
    (CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4)

theorem noSwap_plus_classify (h4 : 4 ≤ Nat.card K) (A : Subgroup (GL (Fin 2 ⊕ Fin 2) K))
    (hA : A ≤ StatedOmega (StatedQuadPlus 2 K)) (hA0 : A ≠ ⊥)
    (hAn : ∀ g ∈ StatedOmega (StatedQuadPlus 2 K), ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hAΩ : A ≠ StatedOmega (StatedQuadPlus 2 K)) :
    A = factorOneKF3p (K := K) ∨ A = factorTwoKF3p (K := K) := by
  haveI := factorOne_isSimple (K := K) h4
  haveI := factorTwo_isSimple (K := K) h4
  have hF1 : factorOneKF3p (K := K) ≤ StatedOmega (StatedQuadPlus 2 K) :=
    factorOne_le_omega h4
  have hF2 : factorTwoKF3p (K := K) ≤ StatedOmega (StatedQuadPlus 2 K) :=
    factorTwo_le_omega h4
  have hΩsup := factorOne_sup_factorTwo h4
  have N1 : (A.subgroupOf (factorOneKF3p (K := K))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hAn (g : GL (Fin 2 ⊕ Fin 2) K) (hF1 g.2) _ hn
    simpa using this⟩
  have N2 : (A.subgroupOf (factorTwoKF3p (K := K))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hAn (g : GL (Fin 2 ⊕ Fin 2) K) (hF2 g.2) _ hn
    simpa using this⟩
  have hB1 : A ⊓ factorOneKF3p (K := K) = ⊥ ∨ factorOneKF3p (K := K) ≤ A := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (A.subgroupOf (factorOneKF3p (K := K))) with h | h
    · exact Or.inl (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h))
    · exact Or.inr (Subgroup.subgroupOf_eq_top.mp h)
  have hB2 : A ⊓ factorTwoKF3p (K := K) = ⊥ ∨ factorTwoKF3p (K := K) ≤ A := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (A.subgroupOf (factorTwoKF3p (K := K))) with h | h
    · exact Or.inl (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h))
    · exact Or.inr (Subgroup.subgroupOf_eq_top.mp h)
  rcases hB1 with h1 | h1 <;> rcases hB2 with h2 | h2
  ·
    exfalso
    apply hA0
    rw [eq_bot_iff]
    intro a ha
    have hcF1 : ∀ f ∈ factorOneKF3p (K := K), a * f = f * a := by
      intro f hf
      have h3 : f * a⁻¹ * f⁻¹ ∈ A := hAn f (hF1 hf) a⁻¹ (A.inv_mem ha)
      have h4' : a * f * a⁻¹ ∈ factorOneKF3p (K := K) := factorOne_normalizes h4 (hA ha) hf
      have hmem : a * (f * a⁻¹ * f⁻¹) ∈ A ⊓ factorOneKF3p (K := K) := by
        refine ⟨A.mul_mem ha h3, ?_⟩
        have e : a * (f * a⁻¹ * f⁻¹) = a * f * a⁻¹ * f⁻¹ := by group
        rw [e]
        exact (factorOneKF3p (K := K)).mul_mem h4' ((factorOneKF3p (K := K)).inv_mem hf)
      rw [h1, Subgroup.mem_bot] at hmem
      calc a * f = (a * (f * a⁻¹ * f⁻¹)) * (f * a) := by group
        _ = f * a := by rw [hmem, one_mul]
    have hcF2 : ∀ f ∈ factorTwoKF3p (K := K), a * f = f * a := by
      intro f hf
      have h3 : f * a⁻¹ * f⁻¹ ∈ A := hAn f (hF2 hf) a⁻¹ (A.inv_mem ha)
      have h4' : a * f * a⁻¹ ∈ factorTwoKF3p (K := K) := factorTwo_normalizes h4 (hA ha) hf
      have hmem : a * (f * a⁻¹ * f⁻¹) ∈ A ⊓ factorTwoKF3p (K := K) := by
        refine ⟨A.mul_mem ha h3, ?_⟩
        have e : a * (f * a⁻¹ * f⁻¹) = a * f * a⁻¹ * f⁻¹ := by group
        rw [e]
        exact (factorTwoKF3p (K := K)).mul_mem h4' ((factorTwoKF3p (K := K)).inv_mem hf)
      rw [h2, Subgroup.mem_bot] at hmem
      calc a * f = (a * (f * a⁻¹ * f⁻¹)) * (f * a) := by group
        _ = f * a := by rw [hmem, one_mul]
    have hC : StatedOmega (StatedQuadPlus 2 K) ≤ Subgroup.centralizer {a} := by
      rw [← hΩsup]
      refine sup_le (fun f hf => ?_) (fun f hf => ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]
          exact hcF1 f hf
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]
          exact hcF2 f hf
    have hcen : ∀ g ∈ StatedOmega (StatedQuadPlus 2 K), a * g = g * a := fun g hg =>
      Subgroup.mem_centralizer_iff.mp (hC hg) a (Set.mem_singleton a)
    have haΩ : a ∈ StatedOmega (StatedQuadPlus 2 K) := hA ha
    have hz : (⟨a, haΩ⟩ : ↥(StatedOmega (StatedQuadPlus 2 K))) ∈
        Subgroup.center ↥(StatedOmega (StatedQuadPlus 2 K)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (hcen _ g.2).symm
    rw [kfs_center_plus h4, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  ·
    right
    refine le_antisymm ?_ h2
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := plus_sup_decomp h4 (hA ha)
    have hxA : x ∈ A := by
      have := A.mul_mem ha (A.inv_mem (h2 hy))
      simpa using this
    have hx1 : x ∈ A ⊓ factorOneKF3p (K := K) := ⟨hxA, hx⟩
    rw [h1, Subgroup.mem_bot] at hx1
    rw [hx1, one_mul]
    exact hy
  ·
    left
    refine le_antisymm ?_ h1
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := plus_sup_decomp h4 (hA ha)
    have hyA : y ∈ A := by
      have := A.mul_mem (A.inv_mem (h1 hx)) ha
      simpa using this
    have hy1 : y ∈ A ⊓ factorTwoKF3p (K := K) := ⟨hyA, hy⟩
    rw [h2, Subgroup.mem_bot] at hy1
    rw [hy1, mul_one]
    exact hx
  ·
    exfalso
    apply hAΩ
    exact le_antisymm hA (by rw [← hΩsup]; exact sup_le h1 h2)

end Plus

section Coset

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem plus_index_coset (h4 : 4 ≤ Nat.card K)
    (hidx : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)) =
      2 * Nat.card (StatedOmega (StatedQuadPlus 2 K)))
    (ω : GL (Fin 2 ⊕ Fin 2) K) (hω : ω ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)) :
    ω ∈ StatedOmega (StatedQuadPlus 2 K) ∨
      tauGLKF⁻¹ * ω ∈ StatedOmega (StatedQuadPlus 2 K) := by
  have hΩO : StatedOmega (StatedQuadPlus 2 K) ≤
      CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K) := by
    unfold StatedOmega
    refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
    rw [commutatorElement_def]
    exact (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)).mul_mem
      ((CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)).mul_mem
        ((CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)).mul_mem hg hh)
        ((CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)).inv_mem hg))
      ((CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)).inv_mem hh)
  have hindex : ((StatedOmega (StatedQuadPlus 2 K)).subgroupOf
      (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K))).index = 2 := by
    have h1 := Subgroup.card_mul_index
      ((StatedOmega (StatedQuadPlus 2 K)).subgroupOf
        (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩO).toEquiv, hidx] at h1
    have hpos : 0 < Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm 2 _))
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.mp hindex
  have hτO := tauGLKF_mem_isometry (K := K)
  have hτΩ := tauGLKF_not_mem_omega h4 (K := K)
  have haτ : (a : GL (Fin 2 ⊕ Fin 2) K) * tauGLKF ∈ StatedOmega (StatedQuadPlus 2 K) := by
    rcases ha ⟨tauGLKF, hτO⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
    · have := Subgroup.mem_subgroupOf.mp h1
      simpa using this
    · exact absurd (Subgroup.mem_subgroupOf.mp h1) hτΩ
  by_cases hωΩ : ω ∈ StatedOmega (StatedQuadPlus 2 K)
  · exact Or.inl hωΩ
  · right
    have haω : (a : GL (Fin 2 ⊕ Fin 2) K) * ω ∈ StatedOmega (StatedQuadPlus 2 K) := by
      rcases ha ⟨ω, hω⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
      · have := Subgroup.mem_subgroupOf.mp h1
        simpa using this
      · exact absurd (Subgroup.mem_subgroupOf.mp h1) hωΩ
    have e : tauGLKF⁻¹ * ω = ((a : GL (Fin 2 ⊕ Fin 2) K) * tauGLKF)⁻¹ * ((a : GL _ K) * ω) := by
      group
    rw [e]
    exact (StatedOmega (StatedQuadPlus 2 K)).mul_mem
      ((StatedOmega (StatedQuadPlus 2 K)).inv_mem haτ) haω

theorem plus_swap_F1 (h4 : 4 ≤ Nat.card K)
    (hidx : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)) =
      2 * Nat.card (StatedOmega (StatedQuadPlus 2 K)))
    (ω : GL (Fin 2 ⊕ Fin 2) K) (hω : ω ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K))
    (hωn : ∀ a ∈ factorOneKF3p (K := K), ω * a * ω⁻¹ ∈ factorOneKF3p (K := K)) :
    ω ∈ StatedOmega (StatedQuadPlus 2 K) := by
  rcases plus_index_coset h4 hidx ω hω with h | h
  · exact h
  · exfalso
    obtain ⟨w, hw, rfl⟩ : ∃ w ∈ StatedOmega (StatedQuadPlus 2 K), ω = tauGLKF * w :=
      ⟨tauGLKF⁻¹ * ω, h, by group⟩
    have hy1 : rhoLKF3p (uUpKF3p (1 : K)) ∈ factorOneKF3p (K := K) := ⟨_, rfl⟩
    have hwy : w⁻¹ * rhoLKF3p (uUpKF3p (1 : K)) * w ∈ factorOneKF3p (K := K) := by
      have := factorOne_normalizes h4 ((StatedOmega (StatedQuadPlus 2 K)).inv_mem hw) hy1
      simpa using this
    have hconj := hωn _ hwy
    have e : tauGLKF * w * (w⁻¹ * rhoLKF3p (uUpKF3p (1 : K)) * w) * (tauGLKF * w)⁻¹ =
        tauGLKF * rhoLKF3p (uUpKF3p (1 : K)) * tauGLKF⁻¹ := by group
    rw [e] at hconj
    have hF2 : tauGLKF * rhoLKF3p (uUpKF3p (1 : K)) * tauGLKF⁻¹ ∈ factorTwoKF3p (K := K) := by
      rw [tau_lm_tau]
      exact ⟨_, rfl⟩
    have hbot : tauGLKF * rhoLKF3p (uUpKF3p (1 : K)) * tauGLKF⁻¹ ∈
        factorOneKF3p (K := K) ⊓ factorTwoKF3p (K := K) := ⟨hconj, hF2⟩
    rw [factorOne_inf_factorTwo, Subgroup.mem_bot] at hbot
    apply rhoL_uUp_one_ne (K := K)
    calc rhoLKF3p (uUpKF3p (1 : K)) = tauGLKF⁻¹ *
          (tauGLKF * rhoLKF3p (uUpKF3p (1 : K)) * tauGLKF⁻¹) * tauGLKF := by group
      _ = 1 := by rw [hbot]; group

theorem plus_swap_F2 (h4 : 4 ≤ Nat.card K)
    (hidx : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)) =
      2 * Nat.card (StatedOmega (StatedQuadPlus 2 K)))
    (ω : GL (Fin 2 ⊕ Fin 2) K) (hω : ω ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K))
    (hωn : ∀ a ∈ factorTwoKF3p (K := K), ω * a * ω⁻¹ ∈ factorTwoKF3p (K := K)) :
    ω ∈ StatedOmega (StatedQuadPlus 2 K) := by
  rcases plus_index_coset h4 hidx ω hω with h | h
  · exact h
  · exfalso
    obtain ⟨w, hw, rfl⟩ : ∃ w ∈ StatedOmega (StatedQuadPlus 2 K), ω = tauGLKF * w :=
      ⟨tauGLKF⁻¹ * ω, h, by group⟩
    have hy2 : rhoRKF3p (uUpKF3p (1 : K)) ∈ factorTwoKF3p (K := K) := ⟨_, rfl⟩
    have hwy : w⁻¹ * rhoRKF3p (uUpKF3p (1 : K)) * w ∈ factorTwoKF3p (K := K) := by
      have := factorTwo_normalizes h4 ((StatedOmega (StatedQuadPlus 2 K)).inv_mem hw) hy2
      simpa using this
    have hconj := hωn _ hwy
    have e : tauGLKF * w * (w⁻¹ * rhoRKF3p (uUpKF3p (1 : K)) * w) * (tauGLKF * w)⁻¹ =
        tauGLKF * rhoRKF3p (uUpKF3p (1 : K)) * tauGLKF⁻¹ := by group
    rw [e] at hconj
    have hF1 : tauGLKF * rhoRKF3p (uUpKF3p (1 : K)) * tauGLKF⁻¹ ∈ factorOneKF3p (K := K) := by
      rw [tau_rm_tau]
      exact ⟨_, rfl⟩
    have hbot : tauGLKF * rhoRKF3p (uUpKF3p (1 : K)) * tauGLKF⁻¹ ∈
        factorOneKF3p (K := K) ⊓ factorTwoKF3p (K := K) := ⟨hF1, hconj⟩
    rw [factorOne_inf_factorTwo, Subgroup.mem_bot] at hbot
    apply rhoR_uUp_one_ne (K := K)
    calc rhoRKF3p (uUpKF3p (1 : K)) = tauGLKF⁻¹ *
          (tauGLKF * rhoRKF3p (uUpKF3p (1 : K)) * tauGLKF⁻¹) * tauGLKF := by group
      _ = 1 := by rw [hbot]; group

end Coset

section Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem transvection_plus (h4 : 4 ≤ Nat.card K) :
    ∃ r ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K), r * r = 1 ∧
      Matrix.rank ((↑r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1) = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hdot : plusVecKF K ⬝ᵥ plusVecKF K = 0 := by
    rw [plusVecKF_dot, plusVecKF_inl0, plusVecKF_inr0]
    linear_combination h2
  have hsq := one_add_vecMulVec_sq_KF (plusVecKF K) (plusVecKF K) h2 hdot
  refine ⟨⟨_, _, hsq, hsq⟩, Subgroup.subset_closure fun v => plus_transv_isometry v,
    Units.ext hsq, ?_⟩
  show Matrix.rank ((1 + Matrix.vecMulVec (plusVecKF K) (plusVecKF K)) - 1) = 1
  rw [add_sub_cancel_left]
  exact rank_vecMulVec_eq_one_KF _ _ (Sum.inl 0) (Sum.inl 0)
    (by simp [plusVecKF, Pi.single_apply])

theorem transvection_minus {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ r ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c), r * r = 1 ∧
      Matrix.rank ((↑r : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) - 1) = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hsq := one_add_vecMulVec_sq_KF (minusVecKF K) (minusFunKF K b) h2
    (minusFunKF_dot_minusVecKF b)
  refine ⟨⟨_, _, hsq, hsq⟩, Subgroup.subset_closure fun v => minus_transv_isometry b c v,
    Units.ext hsq, ?_⟩
  show Matrix.rank ((1 + Matrix.vecMulVec (minusVecKF K) (minusFunKF K b)) - 1) = 1
  rw [add_sub_cancel_left]
  exact rank_vecMulVec_eq_one_KF _ _ (Sum.inr (Sum.inl mIxKF3p)) (Sum.inl mIxKF3p)
    (by rw [minusVecKF_coord, minusFunKF_coord b]; norm_num)

theorem noSwap_plus (h4 : 4 ≤ Nat.card K) :
    ∀ A : Subgroup (GL (Fin 2 ⊕ Fin 2) K), A ≤ StatedOmega (StatedQuadPlus 2 K) → A ≠ ⊥ →
      (∀ g ∈ StatedOmega (StatedQuadPlus 2 K), ∀ a ∈ A, g * a * g⁻¹ ∈ A) →
      A = StatedOmega (StatedQuadPlus 2 K) ∨
        ∀ ω ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K),
          (∀ a ∈ A, ω * a * ω⁻¹ ∈ A) → ω ∈ StatedOmega (StatedQuadPlus 2 K) := by
  intro A hA hA0 hAn
  by_cases hAΩ : A = StatedOmega (StatedQuadPlus 2 K)
  · exact Or.inl hAΩ
  right
  intro ω hωO hωA
  have hidx := isometry_index_plus h4
  rcases noSwap_plus_classify h4 A hA hA0 hAn hAΩ with rfl | rfl
  · exact plus_swap_F1 h4 hidx ω hωO hωA
  · exact plus_swap_F2 h4 hidx ω hωO hωA

theorem noSwap_minus {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ A : Subgroup (GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K),
      A ≤ StatedOmega (StatedQuadMinus 2 K b c) → A ≠ ⊥ →
      (∀ g ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ a ∈ A, g * a * g⁻¹ ∈ A) →
      A = StatedOmega (StatedQuadMinus 2 K b c) ∨
        ∀ ω ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c),
          (∀ a ∈ A, ω * a * ω⁻¹ ∈ A) → ω ∈ StatedOmega (StatedQuadMinus 2 K b c) := by
  intro A hA hA0 hAn
  have hS : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus 2 K b c)) :=
    open CFSG.ComponentClassification.RankTwoClassical.ORigid in
      isSimpleGroup_statedOmega_quadMinus_of_two_le (le_refl 2) hirr
  left
  haveI : (A.subgroupOf (StatedOmega (StatedQuadMinus 2 K b c))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hAn (g : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) g.2 _ hn
    simpa using this⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (A.subgroupOf (StatedOmega (StatedQuadMinus 2 K b c))) with h | h
  · exfalso
    apply hA0
    exact (inf_eq_left.mpr hA).symm.trans (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h))
  · exact le_antisymm hA (Subgroup.subgroupOf_eq_top.mp h)

end Omega

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end
