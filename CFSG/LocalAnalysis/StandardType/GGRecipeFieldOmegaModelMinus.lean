module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.RankThree.PartOne.AUTSL

namespace RecipeFieldOmega

section Minus

variable {K : Type} [Field K] {n : ℕ}

variable (n) in
@[expose] noncomputable def minusIdx (hn : 1 ≤ n) : LargeEvenMinusIdx (n - 1) ≃ Fin (2 * n) :=
  (Equiv.sumAssoc (Fin (n - 1)) (Fin (n - 1)) (Fin 2)).trans (minusIndexEquiv n hn)

theorem minusIdx_inl_inl (hn : 1 ≤ n) (i : Fin (n - 1)) :
    minusIdx n hn (.inl (.inl i)) = minusIndexEquiv n hn (.inl i) := rfl

theorem minusIdx_inl_inr (hn : 1 ≤ n) (i : Fin (n - 1)) :
    minusIdx n hn (.inl (.inr i)) = minusIndexEquiv n hn (.inr (.inl i)) := rfl

theorem minusIdx_inr_zero (hn : 1 ≤ n) : minusIdx n hn (.inr 0) = tailZero n hn := rfl

theorem minusIdx_inr_one (hn : 1 ≤ n) : minusIdx n hn (.inr 1) = tailOne n hn := rfl

variable (n) in
theorem omegaMinus_eq (b c : K) :
    LargeEvenOmega (LargeEvenQMinus (n - 1) b c) =
      StatedOmega ⇑(TableBOrth.qMinusForm K (n - 1) b c) := by
  rw [TableBOrth.coe_qMinusForm]

theorem reindex_qMinusForm (hn : 1 ≤ n) (b c : K) :
    reindexQuadraticForm (minusIdx n hn) (TableBOrth.qMinusForm K (n - 1) b c) =
      coordinateQuadMinus n K hn b c := by
  ext v
  rw [reindexQuadraticForm_apply, coordinateQuadMinus_apply, TableBOrth.coe_qMinusForm]
  rfl

theorem omega_pow_two_pow_eq [CharP K 2] (b c : K) (k : ℕ) :
    (⟨0, 1⟩ : QuadraticAlgebra K c b) ^ 2 ^ k = ⟨(tailSeq b c k).1, (tailSeq b c k).2⟩ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  induction k with
  | zero => ext <;> simp [tailSeq]
  | succ k ih =>
    rw [pow_succ, pow_mul, ih, sq]
    ext
    · simp only [QuadraticAlgebra.re_mul, tailSeq]
      ring
    · simp only [QuadraticAlgebra.im_mul, tailSeq]
      linear_combination (tailSeq b c k).1 * (tailSeq b c k).2 * h2

variable [CharP K 2]

@[expose] noncomputable def minusEquiv (hn4 : 4 ≤ n) (b c : K) :
    LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)) ≃* matrixDerived (Qm n hn4 b c) :=
  (TableBOrth.projMkEquiv (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) b c)).symm.trans
    ((MulEquiv.subgroupCongr (omegaMinus_eq n b c)).trans
      ((statedMatrixDerivedEquiv (minusIdx n (by omega))
          (TableBOrth.qMinusForm K (n - 1) b c)).trans
        (MulEquiv.subgroupCongr (congrArg matrixDerived (reindex_qMinusForm (by omega) b c)))))

theorem minusEquiv_mk_val (hn4 : 4 ≤ n) (b c : K)
    (h : LargeEvenOmega (LargeEvenQMinus (n - 1) b c)) :
    ((minusEquiv hn4 b c (LargeEvenProjMk _ h) : matrixDerived (Qm n hn4 b c)) :
      GL (Fin (2 * n)) K) =
        reindexMatrixEquiv (minusIdx n (by omega)) (h : GL (LargeEvenMinusIdx (n - 1)) K) := by
  have e : LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)) h =
      TableBOrth.projMkEquiv (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) b c) h :=
    (TableBOrth.projMkEquiv_apply _ h).symm
  rw [e, minusEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, statedMatrixDerivedEquiv_val,
    MulEquiv.subgroupCongr_apply]

omit [CharP K 2] in
theorem proj_surjective_minus (b c : K) :
    Function.Surjective (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))) :=
  QuotientGroup.mk'_surjective _

variable [Finite K]

theorem frobPair_pow_right (hn : 1 ≤ n) {b c : K} (hb : b ≠ 0) (k : ℕ) :
    ((frobPair n hn b c hb ^ k : similarityPairs (coordinateQuadMinus n K hn b c)) :
      coordinateSemilinearGroup (2 * n) K).right = frobeniusEquiv K 2 ^ k := by
  have h := map_pow (SemidirectProduct.rightHom (φ := glFieldAut (Fin (2 * n)) K))
    ((frobPair n hn b c hb : similarityPairs (coordinateQuadMinus n K hn b c)) :
      coordinateSemilinearGroup (2 * n) K) k
  simp only [SemidirectProduct.rightHom_eq_right] at h
  rw [SubmonoidClass.coe_pow, h]
  rfl

theorem frobPair_pow_left_val (hn : 1 ≤ n) {b c : K} (hb : b ≠ 0) (k : ℕ) :
    (((frobPair n hn b c hb ^ k : similarityPairs (coordinateQuadMinus n K hn b c)) :
      coordinateSemilinearGroup (2 * n) K).left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        Matrix.reindex (minusIdx n hn) (minusIdx n hn) (LargeEvenFrobBlock (n - 1) b c k) := by
  set g := ((frobPair n hn b c hb ^ k : similarityPairs (coordinateQuadMinus n K hn b c)) :
    coordinateSemilinearGroup (2 * n) K) with hg
  have hgr : g.right = frobeniusEquiv K 2 ^ k := frobPair_pow_right hn hb k
  have hσ : ∀ x : K, (g.right.symm x) ^ 2 ^ k = x := fun x => by
    rw [← frobeniusEquiv_pow_apply, ← hgr, RingEquiv.apply_symm_apply]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hL : Matrix.mulVec g.left.val w =
      coordinateSemilinearMap g (fun i => g.right.symm (w i)) := by
    rw [coordinateSemilinearMap_apply]
    congr 1
    funext i
    exact (RingEquiv.apply_symm_apply _ _).symm
  rw [hL, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  funext i
  have hpow := frobPair_pow_apply n hn b c hb k (fun i => g.right.symm (w i)) i
  rw [← hg] at hpow
  rw [hpow]
  simp only [hσ]
  obtain ⟨x, rfl⟩ := (minusIdx n hn).surjective i
  simp only [Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rcases x with (x | x) | x
  · rw [minusIdx_inl_inl, ite_eq_right (tailZero_ne_inl n hn x),
      ite_eq_right (tailOne_ne_inl n hn x)]
    simp [LargeEvenFrobBlock, Matrix.fromBlocks_mulVec, minusIdx_inl_inl]
  · rw [minusIdx_inl_inr, ite_eq_right (tailZero_ne_inr n hn x),
      ite_eq_right (tailOne_ne_inr n hn x)]
    simp [LargeEvenFrobBlock, Matrix.fromBlocks_mulVec, minusIdx_inl_inr]
  · fin_cases x
    · simp only [Fin.zero_eta, minusIdx_inr_zero, ite_true]
      simp [LargeEvenFrobBlock, omega_pow_two_pow_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        minusIdx_inr_zero, minusIdx_inr_one]
    · simp only [Fin.mk_one, minusIdx_inr_one, ite_eq_right (tailOne_ne_tailZero n hn), ite_true]
      simp [LargeEvenFrobBlock, omega_pow_two_pow_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        minusIdx_inr_zero, minusIdx_inr_one]

theorem frobAut_pow_apply_val (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : ℕ) (X : matrixDerived (Qm n hn4 b c)) :
    (((AutOm.frobAut hn4 hirr ^ k) X : matrixDerived (Qm n hn4 b c)) : GL (Fin (2 * n)) K) =
      ((frobPair n (by omega) b c (ne_zero_of_irreducible_tail b c hirr) ^ k :
          similarityPairs (coordinateQuadMinus n K (by omega) b c)) :
          coordinateSemilinearGroup (2 * n) K).left *
        glFieldAut (Fin (2 * n)) K (frobeniusEquiv K 2 ^ k) X.val *
        ((frobPair n (by omega) b c (ne_zero_of_irreducible_tail b c hirr) ^ k :
          similarityPairs (coordinateQuadMinus n K (by omega) b c)) :
          coordinateSemilinearGroup (2 * n) K).left⁻¹ := by
  rw [AutOm.frobAut, ← map_pow, conjAct_apply, matrixDerivedConjugation_val, frobPair_pow_right]

theorem frobAut_pow_mk_eq_iff (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : ℕ) (x y : LargeEvenOmega (LargeEvenQMinus (n - 1) b c)) :
    (AutOm.frobAut hn4 hirr ^ k) (minusEquiv hn4 b c (LargeEvenProjMk _ x)) =
        minusEquiv hn4 b c (LargeEvenProjMk _ y) ↔
      ((y : GL (LargeEvenMinusIdx (n - 1)) K) : Matrix _ _ K) * LargeEvenFrobBlock (n - 1) b c k =
        LargeEvenFrobBlock (n - 1) b c k *
          ((x : GL (LargeEvenMinusIdx (n - 1)) K) : Matrix _ _ K).map (· ^ 2 ^ k) := by
  have hn : 1 ≤ n := by omega
  set e := minusIdx n hn
  set L := ((frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k :
    similarityPairs (coordinateQuadMinus n K hn b c)) : coordinateSemilinearGroup (2 * n) K).left
  set σ := frobeniusEquiv K 2 ^ k
  have hσ : (fun s : K => s ^ 2 ^ k) = σ := funext fun s => (frobeniusEquiv_pow_apply k s).symm
  have hL : ((reindexMatrixEquiv e).symm L).val = LargeEvenFrobBlock (n - 1) b c k := by
    rw [reindexMatrixEquiv_symm_val, frobPair_pow_left_val hn]
    rw [← Matrix.reindex_symm]
    exact (Matrix.reindex e e).symm_apply_apply _
  rw [Subtype.ext_iff, frobAut_pow_apply_val, minusEquiv_mk_val, minusEquiv_mk_val,
    mul_inv_eq_iff_eq_mul, ← (reindexMatrixEquiv e).symm.injective.eq_iff, map_mul, map_mul,
    glFieldAut_reindex, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Units.ext_iff,
    Units.val_mul, Units.val_mul, hL, glFieldAut_apply_val, hσ, eq_comm]

theorem graphAut_frobAut_pow (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : ℕ) :
    LargeEvenGraphAut (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))
      (fun h h' =>
        ((h' : GL (LargeEvenMinusIdx (n - 1)) K) : Matrix _ _ K) *
            LargeEvenFrobBlock (n - 1) b c k =
          LargeEvenFrobBlock (n - 1) b c k *
            ((h : GL (LargeEvenMinusIdx (n - 1)) K) : Matrix _ _ K).map (· ^ 2 ^ k))
      ((MulAut.congr (minusEquiv hn4 b c)).symm (AutOm.frobAut hn4 hirr ^ k)) :=
  graphAut_congr_symm _ _ _ fun x y hxy => (frobAut_pow_mk_eq_iff hn4 hirr k x y).2 hxy

theorem exists_frob_mem_minus (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : ℕ) (x : LargeEvenOmega (LargeEvenQMinus (n - 1) b c)) :
    ∃ y : LargeEvenOmega (LargeEvenQMinus (n - 1) b c),
      ((y : GL (LargeEvenMinusIdx (n - 1)) K) : Matrix _ _ K) * LargeEvenFrobBlock (n - 1) b c k =
        LargeEvenFrobBlock (n - 1) b c k *
          ((x : GL (LargeEvenMinusIdx (n - 1)) K) : Matrix _ _ K).map (· ^ 2 ^ k) := by
  set Θ := minusEquiv (K := K) hn4 b c
  obtain ⟨y, hy⟩ := proj_surjective_minus b c
    (Θ.symm ((AutOm.frobAut hn4 hirr ^ k) (Θ (LargeEvenProjMk _ x))))
  refine ⟨y, (frobAut_pow_mk_eq_iff hn4 hirr k x y).1 ?_⟩
  rw [hy, MulEquiv.apply_symm_apply]

theorem congr_minusEquiv_of_mem_phi (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {φ : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))}
    (hφ : φ ∈ LargeEvenPhiQ (n - 1) b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))) :
    ∃ k : ℕ, MulAut.congr (minusEquiv hn4 b c) φ = AutOm.frobAut hn4 hirr ^ k := by
  obtain ⟨k, hk⟩ := hφ
  refine ⟨k, ?_⟩
  rw [← MulEquiv.eq_symm_apply]
  exact eq_of_graphAut (proj_surjective_minus b c) hk (graphAut_frobAut_pow hn4 hirr k)
    (exists_frob_mem_minus hn4 hirr k)

theorem exists_mem_phi_congr_minusEquiv (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ) :
    ∃ φ ∈ LargeEvenPhiQ (n - 1) b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))),
      MulAut.congr (minusEquiv hn4 b c) φ = AutOm.frobAut hn4 hirr ^ k :=
  ⟨_, ⟨k, graphAut_frobAut_pow hn4 hirr k⟩, MulEquiv.apply_symm_apply _ _⟩

end Minus

end RecipeFieldOmega

end CFSG.StandardType
