module

public import CFSG.RankThree.SubgroupLists.SymplecticReducible
public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n : ℕ}

theorem spForm_eq_dotProduct (x y : Fin n ⊕ Fin n → K) :
    spForm n K x y = x ⬝ᵥ (spGram n K *ᵥ y) :=
  Matrix.toBilin'_apply' _ _ _

theorem spForm_isAlt : (spForm n K).IsAlt := spForm_self

theorem mem_statedSp_iff_preserves {A : GL (Fin n ⊕ Fin n) K} :
    A ∈ StatedSp n K ↔ ∀ x y, spForm n K ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x)
      ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y) = spForm n K x y := by
  refine ⟨fun hA x y => spForm_mulVec hA x y, fun h => ?_⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  have hB : (spForm n K).comp (Matrix.toLin' (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
      (Matrix.toLin' (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) = spForm n K := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply]
    exact h x y
  have hM := congrArg LinearMap.BilinForm.toMatrix' hB
  rw [LinearMap.BilinForm.toMatrix'_comp, LinearMap.toMatrix'_toLin', spForm,
    LinearMap.BilinForm.toMatrix'_toBilin'] at hM
  exact hM

@[expose] noncomputable def spTransMat (a : Fin n ⊕ Fin n → K) (c : K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  1 + c • vecMulVec a (spGram n K *ᵥ a)

theorem spTransMat_mulVec (a : Fin n ⊕ Fin n → K) (c : K) (x : Fin n ⊕ Fin n → K) :
    spTransMat a c *ᵥ x = x + (c * spForm n K x a) • a := by
  rw [spTransMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec,
    spForm_eq_dotProduct, dotProduct_comm, op_smul_eq_smul, smul_smul]

theorem spTransMat_mul (a : Fin n ⊕ Fin n → K) (c d : K) :
    spTransMat a c * spTransMat a d = spTransMat a (c + d) := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, spTransMat_mulVec, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, spForm_self, smul_eq_mul, mul_zero, add_zero]
  rw [add_assoc, ← add_smul]
  congr 2
  ring

theorem spTransMat_zero (a : Fin n ⊕ Fin n → K) : spTransMat a 0 = 1 := by
  rw [spTransMat, zero_smul, add_zero]

@[expose] noncomputable def spTrans (a : Fin n ⊕ Fin n → K) (c : K) : GL (Fin n ⊕ Fin n) K where
  val := spTransMat a c
  inv := spTransMat a (-c)
  val_inv := by rw [spTransMat_mul, add_neg_cancel, spTransMat_zero]
  inv_val := by rw [spTransMat_mul, neg_add_cancel, spTransMat_zero]

theorem coe_spTrans (a : Fin n ⊕ Fin n → K) (c : K) :
    ((spTrans a c : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      spTransMat a c :=
  rfl

theorem spTrans_mulVec (a : Fin n ⊕ Fin n → K) (c : K) (x : Fin n ⊕ Fin n → K) :
    ((spTrans a c : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x =
      x + (c * spForm n K x a) • a :=
  spTransMat_mulVec a c x

theorem gl_ext_mulVec {g h : GL (Fin n ⊕ Fin n) K}
    (H : ∀ x, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x =
      (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x) : g = h :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, H]))

theorem spTrans_add (a : Fin n ⊕ Fin n → K) (c d : K) :
    spTrans a c * spTrans a d = spTrans a (c + d) :=
  Units.ext (spTransMat_mul a c d)

theorem spTrans_zero (a : Fin n ⊕ Fin n → K) : spTrans a (0 : K) = 1 :=
  Units.ext (spTransMat_zero a)

theorem spTrans_zero_vec (c : K) : spTrans (0 : Fin n ⊕ Fin n → K) c = 1 :=
  gl_ext_mulVec fun x => by rw [spTrans_mulVec, smul_zero, add_zero, Units.val_one, one_mulVec]

theorem spTrans_npow (a : Fin n ⊕ Fin n → K) (c : K) (k : ℕ) :
    spTrans a c ^ k = spTrans a (k * c) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, spTrans_zero]
  | succ k ih => rw [pow_succ, ih, spTrans_add, Nat.cast_succ, add_mul, one_mul]

theorem spTrans_smul (a : Fin n ⊕ Fin n → K) (l c : K) :
    spTrans (l • a) c = spTrans a (l ^ 2 * c) :=
  gl_ext_mulVec fun x => by
    rw [spTrans_mulVec, spTrans_mulVec, map_smul, smul_eq_mul, smul_smul]
    congr 2
    ring

theorem spTrans_mem_statedSp (a : Fin n ⊕ Fin n → K) (c : K) : spTrans a c ∈ StatedSp n K := by
  rw [mem_statedSp_iff_preserves]
  intro x y
  rw [spTrans_mulVec, spTrans_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    spForm_self]
  have hs : spForm n K a y = - spForm n K y a := by
    rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt]
  rw [hs]
  ring

theorem conj_spTrans {g : GL (Fin n ⊕ Fin n) K} (hg : g ∈ StatedSp n K)
    (a : Fin n ⊕ Fin n → K) (c : K) :
    g * spTrans a c * g⁻¹ = spTrans ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ a) c :=
  gl_ext_mulVec fun x => by
    rw [gl_mulVec_mul, gl_mulVec_mul, spTrans_mulVec, spTrans_mulVec, mulVec_add, mulVec_smul,
      gl_mulVec_inv_mulVec]
    congr 3
    rw [← spForm_mulVec hg, gl_mulVec_inv_mulVec]

open CFSG.LocalAnalysis.ComponentInitial in
theorem mem_statedSp_iff_toLin {A : GL (Fin n ⊕ Fin n) K} :
    A ∈ StatedSp n K ↔ Matrix.GeneralLinearGroup.toLin A ∈ bilinIsometryGroup (spForm n K) := by
  rw [mem_statedSp_iff_preserves, mem_bilinIsometryGroup]
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Alternating in
theorem statedSp_eq_closure_spTrans :
    StatedSp n K =
      Subgroup.closure {g | ∃ (a : Fin n ⊕ Fin n → K) (c : K), g = spTrans a c} := by
  refine le_antisymm (fun A hA => ?_) ((Subgroup.closure_le _).mpr ?_)
  · have h := mem_statedSp_iff_toLin.mp hA
    rw [alternating_transvection_generation spForm_isAlt spForm_nondegenerate] at h
    have h' := Subgroup.mem_map_of_mem
      (Matrix.GeneralLinearGroup.toLin (n := Fin n ⊕ Fin n) (R := K)).symm.toMonoidHom h
    rw [MonoidHom.map_closure] at h'
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h'
    refine Subgroup.closure_mono ?_ h'
    rintro _ ⟨_, ⟨a, c, rfl⟩, rfl⟩
    refine ⟨a, c, ?_⟩
    apply (Matrix.GeneralLinearGroup.toLin (n := Fin n ⊕ Fin n) (R := K)).injective
    rw [MulEquiv.apply_symm_apply]
    apply Units.ext
    refine LinearMap.ext fun x => ?_
    rw [symplecticTransvection_apply, Matrix.GeneralLinearGroup.coe_toLin,
      Matrix.mulVecLin_apply, spTrans_mulVec]
  · rintro _ ⟨a, c, rfl⟩
    exact spTrans_mem_statedSp a c

end CFSG.RankThree.SubgroupLists
