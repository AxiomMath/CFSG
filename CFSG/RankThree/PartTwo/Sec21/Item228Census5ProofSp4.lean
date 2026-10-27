module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofOdd
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofSp4
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpFrame
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpFreeL
import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projSL projSp projImage)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.RankThree.SubgroupLists (plusBlock minusBlock tStdMat)

namespace Item228Census5Proof

open Item228Census3Proof Item211Lie3Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem mem_statedSp_iff_mem_gramGroup {g : GL V₄ K} :
    g ∈ StatedSp 2 K ↔ g ∈ gramGroup (gramStd K) := by
  rw [Item228Census2Proof.mem_statedSp_iff_gram, mem_gramGroup]
  rfl

theorem sq_eq_one_of_scalar_mem_statedSp {u : Kˣ}
    (hu : GeneralLinearGroup.scalar V₄ u ∈ StatedSp 2 K) : u ^ 2 = 1 := by
  have h := Item228Census2Proof.mem_statedSp_iff_gram.mp hu
  rw [GeneralLinearGroup.coe_scalar] at h
  have h' := congrArg (fun M : Matrix V₄ V₄ K => M (Sum.inl 0) (Sum.inr 0)) h
  simp [Matrix.scalar_apply, Matrix.fromBlocks] at h'
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; linear_combination h')

theorem mem_statedSp_conj_iff {h : GL V₄ K} (hh : h ∈ StatedSp 2 K) (g : GL V₄ K) :
    g ∈ StatedSp 2 K ↔ h⁻¹ * g * h ∈ StatedSp 2 K := by
  rw [Subgroup.mul_mem_cancel_right _ hh, Subgroup.mul_mem_cancel_left _ (inv_mem hh)]

variable (K) in
@[expose] def permPlaneMat : Matrix V₄ V₄ K :=
  fromBlocks !![0, 0; 1, 0] !![1, 0; 0, 0] !![0, 0; 0, 1] !![0, 1; 0, 0]

theorem permPlaneMat_transpose_mul : (permPlaneMat K)ᵀ * permPlaneMat K = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [permPlaneMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks]

theorem permPlaneMat_mul_transpose : permPlaneMat K * (permPlaneMat K)ᵀ = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [permPlaneMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks]

variable (K) in
@[expose] def permPlane : GL V₄ K where
  val := permPlaneMat K
  inv := (permPlaneMat K)ᵀ
  val_inv := permPlaneMat_mul_transpose
  inv_val := permPlaneMat_transpose_mul

theorem permPlane_gram :
    ((permPlane K : GL V₄ K) : Matrix V₄ V₄ K)ᵀ * gramStd K * (permPlane K : GL V₄ K) =
      gramPlane K := by
  change (permPlaneMat K)ᵀ * gramStd K * permPlaneMat K = gramPlane K
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [permPlaneMat, gramStd, gramPlane, symJ2, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, fromBlocks]

theorem permPlane_conj (h2 : (2 : K) ≠ 0) {X : Matrix V₄ V₄ K}
    (hX : X * tStdMat = tStdMat * X) :
    (((permPlane K)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * X * (permPlane K : GL V₄ K) =
      fromBlocks (minusBlock X) 0 0 (plusBlock X) := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := offBlock_eq_zero h2 hX
  change (permPlaneMat K)ᵀ * X * permPlaneMat K = _
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [permPlaneMat, minusBlock, plusBlock, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, fromBlocks, z1, z2, z3, z4, z5, z6, z7, z8]

theorem jStd_eq :
    (jStd : Matrix V₄ V₄ K) = fromBlocks !![0, -3; 1, 0] 0 0 !![0, -1; 3, 0] := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [jStd, xiMat, fromBlocks]

variable (K) in
@[expose] noncomputable def frameTensorMat : Matrix V₄ V₄ K :=
  fromBlocks !![2, -1; 0, 1] 0 0 !![1, -2⁻¹; 0, 3 * 2⁻¹]

variable (K) in
@[expose] noncomputable def frameTensorInvMat : Matrix V₄ V₄ K :=
  fromBlocks !![2⁻¹, 2⁻¹; 0, 1] 0 0 !![1, 3⁻¹; 0, 2 * 3⁻¹]

theorem frameTensorMat_mul_inv (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    frameTensorMat K * frameTensorInvMat K = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [frameTensorMat, frameTensorInvMat, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, fromBlocks] <;> field_simp <;> ring

theorem frameTensorInv_mul (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    frameTensorInvMat K * frameTensorMat K = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [frameTensorMat, frameTensorInvMat, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, fromBlocks] <;> field_simp
  ring

@[expose] noncomputable def frameTensor (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : GL V₄ K where
  val := frameTensorMat K
  inv := frameTensorInvMat K
  val_inv := frameTensorMat_mul_inv h2 h3
  inv_val := frameTensorInv_mul h2 h3

theorem frameTensor_gram (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    ((frameTensor h2 h3 : GL V₄ K) : Matrix V₄ V₄ K)ᵀ * gramStd K *
      (frameTensor h2 h3 : GL V₄ K) = gramTensor K := by
  change (frameTensorMat K)ᵀ * gramStd K * frameTensorMat K = gramTensor K
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [frameTensorMat, gramStd, gramTensor, gramS, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, fromBlocks] <;> field_simp <;> ring

theorem jStd_mul_frameTensorMat (h2 : (2 : K) ≠ 0) :
    (2⁻¹ : K) • (jStd - 1) * frameTensorMat K =
      frameTensorMat K * fromBlocks (cubeMat K) 0 0 (cubeMat K) := by
  rw [jStd_eq]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [frameTensorMat, cubeMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      fromBlocks, Matrix.one_apply] <;> field_simp <;> ring

theorem centData_statedSp [Finite K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {A : GL V₄ K}
    (hA : A ∈ StatedSp 2 K) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    (∃ φ : SpecialLinearGroup (Fin 2) K →* GL V₄ K, IsCentData (StatedSp 2 K) A φ ∧
        (ProjGenLinGroup.mk.comp φ).ker = ⊥) ∨
      (∃ φ : SpecialLinearGroup (Fin 2) K →* GL V₄ K, IsCentData (StatedSp 2 K) A φ ∧
        (ProjGenLinGroup.mk.comp φ).ker = Subgroup.center (SpecialLinearGroup (Fin 2) K)) := by
  have hA3m : (A : Matrix V₄ V₄ K) * A * A = 1 := by
    have e := congrArg Units.val hA3
    rwa [Units.val_pow_eq_pow_val, pow_three, ← Matrix.mul_assoc, Units.val_one] at e
  by_cases hP : (A : Matrix V₄ V₄ K) * A + A + 1 = 0
  ·
    right
    obtain ⟨h, hh, hj⟩ := exists_frame_free h2 h3 (spForm_skew_of_root hA hP)
      (mulVec_sq_of_root hP)
    set F := frameTensor h2 h3 with hF
    set P : GL V₄ K := F⁻¹ * h⁻¹ with hPdef
    have hHH : ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (h : Matrix V₄ V₄ K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hconjA : ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (A : Matrix V₄ V₄ K) *
        (h : Matrix V₄ V₄ K) = (2⁻¹ : K) • (jStd - 1) := by
      have e : ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * ((2 : K) • (A : Matrix V₄ V₄ K) + 1) *
          (h : Matrix V₄ V₄ K) = jStd := by
        rw [Matrix.mul_assoc, hj, ← Matrix.mul_assoc, hHH, Matrix.one_mul]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        hHH] at e
      rw [← e, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ h2, one_smul]
    have hD : ((P * A * P⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
        fromBlocks (cubeMat K) 0 0 (cubeMat K) := by
      have e1 : P * A * P⁻¹ = F⁻¹ * (h⁻¹ * A * h) * F := by
        rw [hPdef]
        group
      rw [e1]
      simp only [Units.val_mul]
      rw [hconjA]
      change frameTensorInvMat K * ((2⁻¹ : K) • (jStd - 1)) * frameTensorMat K = _
      rw [Matrix.mul_assoc, jStd_mul_frameTensorMat h2, ← Matrix.mul_assoc,
        frameTensorInv_mul h2 h3, Matrix.one_mul]
    refine ⟨_, (isCentData_tensor h2 h3 hD).conj (fun g => ?_) rfl, ?_⟩
    · rw [mem_statedSp_conj_iff hh, mem_statedSp_iff_mem_gramGroup,
        mem_gramGroup_conj_iff (frameTensor_gram h2 h3)]
      have e : F⁻¹ * (h⁻¹ * g * h) * F⁻¹⁻¹ = P * g * P⁻¹ := by
        rw [hPdef]
        group
      rw [e]
    · rw [ker_mk_conj, ker_mk_iotaTensor]
  ·
    left
    obtain ⟨h, hh, hfr, hplus, hminus⟩ := exists_frame h2 h3 hA hA3m hA1 hP
    set P : GL V₄ K := (permPlane K)⁻¹ * h⁻¹ with hPdef
    have hD0 : ((h⁻¹ * A * h : GL V₄ K) : Matrix V₄ V₄ K) = frConj h (A : Matrix V₄ V₄ K) := rfl
    have hD0t : ((h⁻¹ * A * h : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat =
        tStdMat * ((h⁻¹ * A * h : GL V₄ K) : Matrix V₄ V₄ K) := by
      rw [hD0]
      exact hfr _ rfl
    have hD0S : h⁻¹ * A * h ∈ StatedSp 2 K := (mem_statedSp_conj_iff hh A).mp hA
    have hdet : (minusBlock (frConj h (A : Matrix V₄ V₄ K))).det = 1 := by
      rw [← hD0]
      exact det_minusBlock h2 hD0S hD0t
    have hD : ((P * A * P⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
        fromBlocks (minusBlock (frConj h (A : Matrix V₄ V₄ K))) 0 0 1 := by
      have e1 : P * A * P⁻¹ = (permPlane K)⁻¹ * (h⁻¹ * A * h) * permPlane K := by
        rw [hPdef]
        group
      rw [e1, Units.val_mul, Units.val_mul, permPlane_conj h2 hD0t, hD0, hplus]
    refine ⟨_, (isCentData_plane h3 hdet hminus hD).conj (fun g => ?_) rfl, ?_⟩
    · rw [mem_statedSp_conj_iff hh, mem_statedSp_iff_mem_gramGroup,
        mem_gramGroup_conj_iff permPlane_gram]
      have e : (permPlane K)⁻¹ * (h⁻¹ * g * h) * (permPlane K)⁻¹⁻¹ = P * g * P⁻¹ := by
        rw [hPdef]
        group
      rw [e]
    · rw [ker_mk_conj, ker_mk_iotaPlane]

theorem three_ne_zero_galoisField {p e : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) :
    (3 : GaloisField p e) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff (GaloisField p e) p 3).mp (by exact_mod_cast h)
  exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp this)

end Item228Census5Proof

open Item228Census3Proof Item228Census5Proof

theorem pSp4OddCentThree_holds : PSp4OddCentThree := by
  intro p _ hp _ y hy
  have hp' : p.Prime := Fact.out
  set K := GaloisField p 1
  have hKc : Nat.card K = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have h2 : (2 : K) ≠ 0 := Item228Census2Proof.two_ne_zero_galoisField (by omega)
  have h3 : (3 : K) ≠ 0 := three_ne_zero_galoisField (by omega)
  set G := StatedSp 2 K with hG
  have hZ4 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) u ∈ G → u ^ 4 = 1 := by
    intro u hu
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_eq_one_of_scalar_mem_statedSp hu, one_pow]
  have hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) u ∈ G → u ^ 3 = 1 → u = 1 :=
    fun u hu h3' => by
      calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
        _ = 1 := by rw [hZ4 u hu, h3', inv_one, one_mul]
  obtain ⟨A, hAy, hA3, hA1⟩ := exists_lift_cube G hZ4 y hy
  have hA3' : (A : GL (Fin 2 ⊕ Fin 2) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hA3, Subgroup.coe_one]
  have hA1' : (A : GL (Fin 2 ⊕ Fin 2) K) ≠ 1 := fun h => hA1 (Subtype.ext h)
  rcases centData_statedSp h2 h3 A.2 hA3' hA1' with ⟨φ, hφ, hker⟩ | ⟨φ, hφ, hker⟩
  · left
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
      CFSG.ClassicalInvolution.sl2_isPerfect (by rw [hKc]; omega)
    obtain ⟨e⟩ := nonempty_perfectResidual_equiv_of_ker_bot G A hA3 hZ3 φ hφ hker
    rw [hAy] at e
    exact ⟨e⟩
  · right
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
      CFSG.ClassicalInvolution.sl2_isPerfect (by rw [hKc]; omega)
    obtain ⟨e⟩ := nonempty_perfectResidual_equiv_projSL G A hA3 hZ3 φ hφ hker (MulEquiv.refl _)
    rw [hAy] at e
    exact ⟨e⟩

theorem census228PSp4Odd_holds : Census228PSp4Odd :=
  census228PSp4Odd_of pSp4OddCentThree_holds

end CFSG.RankThree.PartTwo.Sec21
