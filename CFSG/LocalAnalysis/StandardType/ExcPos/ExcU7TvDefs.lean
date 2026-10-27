module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.RankThree.Classical2.SLnRootAutomorphism
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos.ExcU7

open Matrix CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
open scoped MatrixGroups

variable {L : Type} [Field L] {ν : ℕ}

@[expose] def tvMat (v φ : Fin ν → L) (t : L) : Matrix (Fin ν) (Fin ν) L :=
  1 + t • Matrix.vecMulVec v φ

@[expose] def tvGroup (v φ : Fin ν → L) : Subgroup SL(ν, L) :=
  Subgroup.closure {X : SL(ν, L) | ∃ t : L, (X : Matrix (Fin ν) (Fin ν) L) = tvMat v φ t}

@[expose] def IsTvGroup (T : Subgroup SL(ν, L)) : Prop :=
  ∃ v φ : Fin ν → L, v ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ v = 0 ∧ T = tvGroup v φ

@[expose] def IsSwappedTv (Φ : SL(ν, L) →* SL(ν, L)) (T : Subgroup SL(ν, L)) : Prop :=
  (T.map Φ).map Φ = T ∧ (∀ x ∈ T, ∀ y ∈ T.map Φ, x * y = y * x) ∧ T ≠ T.map Φ

private theorem u7tv_vecMulVec_mul_self {v φ : Fin ν → L} (h : φ ⬝ᵥ v = 0) :
    Matrix.vecMulVec v φ * Matrix.vecMulVec v φ = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]

private theorem u7tv_one_add_smul_mul (N : Matrix (Fin ν) (Fin ν) L) (hN : N * N = 0) (s t : L) :
    (1 + s • N) * (1 + t • N) = 1 + (s + t) • N := by
  have hst : (s • N) * (t • N) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero, smul_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, hst, add_zero,
    add_assoc, ← add_smul]

private theorem u7tv_inv_one_add_smul (N : Matrix (Fin ν) (Fin ν) L) (hN : N * N = 0) (s : L) :
    (1 + s • N)⁻¹ = 1 - s • N := by
  refine Matrix.inv_eq_right_inv ?_
  rw [sub_eq_add_neg, ← neg_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero, add_zero, add_assoc, ← add_smul,
    add_neg_cancel, zero_smul]

private theorem u7tv_det_tvMat (v φ : Fin ν → L) (t : L) :
    (tvMat v φ t).det = 1 + t * (φ ⬝ᵥ v) := by
  rw [tvMat, ← smul_vecMulVec, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct_smul, smul_eq_mul]

private theorem u7tv_map_tvMat (σ : L →+* L) (v φ : Fin ν → L) (t : L) :
    (tvMat v φ t).map σ = tvMat (fun i => σ (v i)) (fun i => σ (φ i)) (σ t) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [tvMat, Matrix.map_apply, Matrix.one_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      mul_assoc]
  · simp [tvMat, Matrix.map_apply, Matrix.one_apply, Matrix.vecMulVec_apply, hij,
      smul_eq_mul, mul_assoc]

private theorem u7tv_stdUnitary_tvMat_apply (σ : L →+* L) (v φ : Fin ν → L)
    (h : φ ⬝ᵥ v = 0) (t : L) :
    (((tvMat v φ t).map σ)⁻¹)ᵀ =
      tvMat (fun i => σ (φ i)) (fun i => σ (v i)) (-(σ t)) := by
  have h0 : (fun i => σ (φ i)) ⬝ᵥ (fun i => σ (v i)) = 0 := by
    change (σ ∘ φ) ⬝ᵥ (σ ∘ v) = 0
    rw [← RingHom.map_dotProduct σ φ v, h, map_zero]
  have hN : Matrix.vecMulVec (fun i => σ (φ i)) (fun i => σ (v i)) *
      Matrix.vecMulVec (fun i => σ (φ i)) (fun i => σ (v i)) = 0 :=
    u7tv_vecMulVec_mul_self (by rw [dotProduct_comm]; exact h0)
  rw [u7tv_map_tvMat]
  simp only [tvMat]
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_smul, Matrix.transpose_vecMulVec]
  rw [u7tv_inv_one_add_smul _ hN]
  simp only [neg_smul, sub_eq_add_neg]

private theorem u7tv_sl_mul_inv (k : SL(ν, L)) :
    (k : Matrix (Fin ν) (Fin ν) L) * ((k⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

private theorem u7tv_conj_tvMat (M : GL (Fin ν) L) (v φ : Fin ν → L) (t : L) :
    (M : Matrix (Fin ν) (Fin ν) L) * tvMat v φ t *
        ((M⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
      tvMat ((M : Matrix (Fin ν) (Fin ν) L).mulVec v)
        (Matrix.vecMul φ ((M⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) t := by
  simp only [tvMat]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, M.mul_inv]

private theorem u7tv_sl_conj_tvMat (k : SL(ν, L)) (v φ : Fin ν → L) (t : L) :
    (k : Matrix (Fin ν) (Fin ν) L) * tvMat v φ t *
        ((k⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      tvMat ((k : Matrix (Fin ν) (Fin ν) L).mulVec v)
        (Matrix.vecMul φ ((k⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L)) t := by
  simp only [tvMat]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, u7tv_sl_mul_inv]

private theorem u7tv_conjSLn_mul_apply (M N : GL (Fin ν) L) (X : SL(ν, L)) :
    conjSLn (M * N) X = conjSLn M (conjSLn N X) := by
  apply Subtype.ext
  rw [coe_conjSLn, coe_conjSLn, coe_conjSLn, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

private theorem u7tv_conjSLn_one_apply (X : SL(ν, L)) :
    conjSLn (1 : GL (Fin ν) L) X = X := by
  apply Subtype.ext
  rw [coe_conjSLn]
  simp

private theorem u7tv_conjSLn_comp_inv (M : GL (Fin ν) L) (X : SL(ν, L)) :
    conjSLn M (conjSLn M⁻¹ X) = X := by
  rw [← u7tv_conjSLn_mul_apply, mul_inv_cancel, u7tv_conjSLn_one_apply]

private theorem u7tv_gl_inv_mulVec (M : GL (Fin ν) L) (v : Fin ν → L) :
    (((M⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)).mulVec
        (((M : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem u7tv_gl_inv_vecMul (M : GL (Fin ν) L) (φ : Fin ν → L) :
    (Matrix.vecMul φ ((M⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) ᵥ*
        (((M⁻¹ : GL (Fin ν) L)⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) = φ := by
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

private theorem u7tv_sl_inv_mulVec (k : SL(ν, L)) (v : Fin ν → L) :
    (((k⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L)).mulVec
        (((k : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

private theorem u7tv_sl_inv_vecMul (k : SL(ν, L)) (φ : Fin ν → L) :
    (Matrix.vecMul φ ((k⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L)) ᵥ*
        (((k⁻¹ : SL(ν, L))⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) = φ := by
  rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

private theorem u7tv_mulAut_conj_comp_inv (k : SL(ν, L)) (X : SL(ν, L)) :
    (MulAut.conj k) ((MulAut.conj k⁻¹) X) = X := by
  rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  group

private theorem u7tv_vecMulVec_single {a b : Fin ν} :
    Matrix.vecMulVec (Pi.single a (1 : L)) (Pi.single b (1 : L)) =
      Matrix.single a b 1 :=
  (Matrix.single_eq_single_vecMulVec_single a b).symm

private theorem u7tv_tvMat_single {a b : Fin ν} (hab : a ≠ b) (t : L) :
    tvMat (Pi.single a (1 : L)) (Pi.single b (1 : L)) t =
      (Matrix.SpecialLinearGroup.transvection hab t : Matrix (Fin ν) (Fin ν) L) := by
  rw [tvMat, u7tv_vecMulVec_single, Matrix.smul_single,
    Matrix.SpecialLinearGroup.transvection_coe]
  congr 1
  ext i j
  simp

private theorem u7tv_tvMat_smul_smul (a b t : L) (v φ : Fin ν → L) :
    tvMat (a • v) (b • φ) t = tvMat v φ (t * (a * b)) := by
  have hN : Matrix.vecMulVec (a • v) (b • φ) = (a * b) • Matrix.vecMulVec v φ := by
    rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
  rw [tvMat, tvMat, hN, smul_smul]

private theorem u7tv_tvGroup_smul {v φ : Fin ν → L} {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    tvGroup (a • v) (b • φ) = tvGroup v φ := by
  apply le_antisymm
  · rw [tvGroup, Subgroup.closure_le]
    rintro X ⟨t, ht⟩
    exact Subgroup.subset_closure ⟨t * (a * b), by rw [ht, u7tv_tvMat_smul_smul]⟩
  · rw [tvGroup, Subgroup.closure_le]
    rintro X ⟨t, ht⟩
    refine Subgroup.subset_closure ⟨t * (a * b)⁻¹, ?_⟩
    rw [ht, u7tv_tvMat_smul_smul a b (t * (a * b)⁻¹)]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ (mul_ne_zero ha hb), mul_one]

private theorem u7tv_exists_smul_of_vecMulVec_eq {a b c d : Fin ν → L}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Matrix.vecMulVec a b = Matrix.vecMulVec c d) :
    ∃ α β : L, α ≠ 0 ∧ β ≠ 0 ∧ c = α • a ∧ d = β • b := by
  have hentry : ∀ i j, a i * b j = c i * d j := by
    intro i j
    have := congrFun (congrFun h i) j
    simpa only [Matrix.vecMulVec_apply] using this
  have hc : c ≠ 0 := by
    intro hc
    have hzero : Matrix.vecMulVec a b = 0 := by rw [h, hc, Matrix.zero_vecMulVec]
    rw [Matrix.vecMulVec_eq_zero] at hzero
    exact hzero.elim ha hb
  have hd : d ≠ 0 := by
    intro hd
    have hzero : Matrix.vecMulVec a b = 0 := by rw [h, hd, Matrix.vecMulVec_zero]
    rw [Matrix.vecMulVec_eq_zero] at hzero
    exact hzero.elim ha hb
  obtain ⟨j₁, hj₁⟩ := Function.ne_iff.mp hd
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.mp hc
  have hbj₁ : b j₁ ≠ 0 := by
    intro hbj
    have h0 : c i₁ * d j₁ = 0 := by rw [← hentry i₁ j₁, hbj, mul_zero]
    exact (mul_ne_zero hi₁ hj₁) h0
  have hai₁ : a i₁ ≠ 0 := by
    intro hai
    have h0 : c i₁ * d j₁ = 0 := by rw [← hentry i₁ j₁, hai, zero_mul]
    exact (mul_ne_zero hi₁ hj₁) h0
  refine ⟨b j₁ / d j₁, a i₁ / c i₁, div_ne_zero hbj₁ hj₁, div_ne_zero hai₁ hi₁, ?_, ?_⟩
  · funext i
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hj₁, mul_comm (b j₁) (a i),
      ← hentry i j₁]
  · funext j
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hi₁, hentry i₁ j,
      mul_comm (d j) (c i₁)]

theorem mem_tvGroup_iff {v φ : Fin ν → L} (h : φ ⬝ᵥ v = 0) {X : SL(ν, L)} :
    X ∈ tvGroup v φ ↔ ∃ t : L, (X : Matrix (Fin ν) (Fin ν) L) = tvMat v φ t := by
  constructor
  · intro hX
    refine Subgroup.closure_induction (p := fun (X : SL(ν, L)) _ =>
      ∃ t : L, (X : Matrix (Fin ν) (Fin ν) L) = tvMat v φ t) ?_ ?_ ?_ ?_ hX
    · rintro X ⟨t, ht⟩
      exact ⟨t, ht⟩
    · exact ⟨0, by simp [tvMat]⟩
    · rintro X Y _ _ ⟨s, hs⟩ ⟨t, ht⟩
      refine ⟨s + t, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_mul, hs, ht]
      simp only [tvMat]
      rw [u7tv_one_add_smul_mul _ (u7tv_vecMulVec_mul_self h)]
    · rintro X _ ⟨s, hs⟩
      refine ⟨-s, ?_⟩
      rw [CFSG.RankThree.Classical2.coe_inv_eq_nonsing_inv, hs]
      simp only [tvMat]
      rw [u7tv_inv_one_add_smul _ (u7tv_vecMulVec_mul_self h)]
      simp only [neg_smul, sub_eq_add_neg]
  · rintro ⟨t, ht⟩
    rw [tvGroup]
    exact Subgroup.subset_closure ⟨t, ht⟩

theorem mem_tvGroup_single {a b : Fin ν} (hab : a ≠ b) {X : SL(ν, L)} :
    X ∈ tvGroup (Pi.single a (1 : L)) (Pi.single b (1 : L)) ↔
      ∃ t : L, X = Matrix.SpecialLinearGroup.transvection hab t := by
  have hdot : (Pi.single b (1 : L) : Fin ν → L) ⬝ᵥ (Pi.single a (1 : L) : Fin ν → L) = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hab.symm]
  rw [mem_tvGroup_iff hdot]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Subtype.ext (ht.trans (u7tv_tvMat_single hab t))⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, (u7tv_tvMat_single hab t).symm⟩

theorem tvGroup_map_conjSLn {v φ : Fin ν → L} (h : φ ⬝ᵥ v = 0) (M : GL (Fin ν) L) :
    (tvGroup v φ).map (conjSLn M) =
      tvGroup ((M : Matrix (Fin ν) (Fin ν) L).mulVec v)
        (Matrix.vecMul φ ((M⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, tvGroup, Subgroup.closure_le]
    rintro X ⟨t, ht⟩
    change (conjSLn M) X ∈ tvGroup ((M : Matrix (Fin ν) (Fin ν) L).mulVec v)
      (Matrix.vecMul φ ((M⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L))
    exact Subgroup.subset_closure ⟨t, by rw [coe_conjSLn, ht, u7tv_conj_tvMat]⟩
  · rw [tvGroup, Subgroup.closure_le]
    rintro Y ⟨t, ht⟩
    change ∃ x ∈ tvGroup v φ, conjSLn M x = Y
    refine ⟨conjSLn M⁻¹ Y, Subgroup.subset_closure ⟨t, ?_⟩,
      u7tv_conjSLn_comp_inv M Y⟩
    rw [coe_conjSLn, ht, u7tv_conj_tvMat M⁻¹ ((M : Matrix (Fin ν) (Fin ν) L).mulVec v)
      (Matrix.vecMul φ ((M⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) t]
    rw [u7tv_gl_inv_mulVec, u7tv_gl_inv_vecMul]

theorem tvGroup_map_conj {v φ : Fin ν → L} (h : φ ⬝ᵥ v = 0) (k : SL(ν, L)) :
    (tvGroup v φ).map (MulAut.conj k).toMonoidHom =
      tvGroup ((k : Matrix (Fin ν) (Fin ν) L).mulVec v)
        (Matrix.vecMul φ ((k⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L)) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, tvGroup, Subgroup.closure_le]
    rintro X ⟨t, ht⟩
    change (MulAut.conj k).toMonoidHom X ∈ tvGroup
      ((k : Matrix (Fin ν) (Fin ν) L).mulVec v)
      (Matrix.vecMul φ ((k⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L))
    exact Subgroup.subset_closure ⟨t, by
      show ((MulAut.conj k) X : Matrix (Fin ν) (Fin ν) L) =
        tvMat ((k : Matrix (Fin ν) (Fin ν) L).mulVec v)
          (Matrix.vecMul φ ((k⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L)) t
      rw [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, ht]
      exact u7tv_sl_conj_tvMat k v φ t⟩
  · rw [tvGroup, Subgroup.closure_le]
    rintro Y ⟨t, ht⟩
    change ∃ x ∈ tvGroup v φ, (MulAut.conj k).toMonoidHom x = Y
    refine ⟨(MulAut.conj k⁻¹) Y, Subgroup.subset_closure ⟨t, ?_⟩,
      u7tv_mulAut_conj_comp_inv k Y⟩
    show ((MulAut.conj k⁻¹) Y : Matrix (Fin ν) (Fin ν) L) = tvMat v φ t
    rw [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, ht]
    rw [u7tv_sl_conj_tvMat k⁻¹ ((k : Matrix (Fin ν) (Fin ν) L).mulVec v)
      (Matrix.vecMul φ ((k⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L)) t]
    rw [u7tv_sl_inv_mulVec, u7tv_sl_inv_vecMul]

theorem tvGroup_map_stdUnitary {v φ : Fin ν → L} (h : φ ⬝ᵥ v = 0) (σ : L ≃+* L) :
    (tvGroup v φ).map (stdUnitary σ.toRingHom) =
      tvGroup (fun i => σ (φ i)) (fun i => σ (v i)) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, tvGroup, Subgroup.closure_le]
    rintro X ⟨t, ht⟩
    change stdUnitary σ.toRingHom X ∈ tvGroup (fun i => σ (φ i)) (fun i => σ (v i))
    exact Subgroup.subset_closure ⟨-(σ t), by
      rw [coe_stdUnitary, ht]
      exact u7tv_stdUnitary_tvMat_apply σ.toRingHom v φ h t⟩
  · rw [tvGroup, Subgroup.closure_le]
    rintro Y ⟨s, hs⟩
    let X : SL(ν, L) := ⟨tvMat v φ (-(σ.symm s)),
      by rw [u7tv_det_tvMat, h, mul_zero, add_zero]⟩
    refine (Subgroup.mem_map (f := stdUnitary σ.toRingHom) (K := tvGroup v φ)).mpr
      ⟨X, Subgroup.subset_closure ⟨-(σ.symm s), rfl⟩, ?_⟩
    apply Subtype.ext
    rw [coe_stdUnitary, hs]
    show (((tvMat v φ (-(σ.symm s))).map σ.toRingHom)⁻¹)ᵀ =
      tvMat (fun i => σ (φ i)) (fun i => σ (v i)) s
    rw [u7tv_stdUnitary_tvMat_apply σ.toRingHom v φ h (-(σ.symm s))]
    change tvMat (fun i => σ (φ i)) (fun i => σ (v i)) (-(σ (-(σ.symm s)))) =
      tvMat (fun i => σ (φ i)) (fun i => σ (v i)) s
    rw [show -(σ (-(σ.symm s))) = s by rw [map_neg, σ.apply_symm_apply, neg_neg]]

theorem tvGroup_eq_iff {v φ v' φ' : Fin ν → L} (hv : v ≠ 0) (hφ : φ ≠ 0) (hv' : v' ≠ 0)
    (hφ' : φ' ≠ 0) (h : φ ⬝ᵥ v = 0) (h' : φ' ⬝ᵥ v' = 0) :
    tvGroup v φ = tvGroup v' φ' ↔ ∃ a b : L, a ≠ 0 ∧ b ≠ 0 ∧ v' = a • v ∧ φ' = b • φ := by
  constructor
  · intro hEq
    let X : SL(ν, L) := ⟨tvMat v φ 1, by rw [u7tv_det_tvMat, h, mul_zero, add_zero]⟩
    have hX : X ∈ tvGroup v φ := Subgroup.subset_closure ⟨1, rfl⟩
    obtain ⟨s, hs⟩ := (mem_tvGroup_iff h').mp (hEq ▸ hX)
    have hmat : Matrix.vecMulVec v φ = s • Matrix.vecMulVec v' φ' := by
      have h1 := hs
      change tvMat v φ 1 = tvMat v' φ' s at h1
      simp only [tvMat, one_smul] at h1
      exact add_left_cancel h1
    have hs0 : s ≠ 0 := by
      intro hs0
      have hzero : Matrix.vecMulVec v φ = 0 := by rw [hmat, hs0, zero_smul]
      rw [Matrix.vecMulVec_eq_zero] at hzero
      exact hzero.elim hv hφ
    have hmat' : Matrix.vecMulVec v φ = Matrix.vecMulVec (s • v') φ' := by
      rw [hmat, Matrix.smul_vecMulVec]
    obtain ⟨α, β, hα, hβ, hc, hd⟩ := u7tv_exists_smul_of_vecMulVec_eq hv hφ hmat'
    refine ⟨s⁻¹ * α, β, mul_ne_zero (inv_ne_zero hs0) hα, hβ, ?_, hd⟩
    have h1 : s⁻¹ • (s • v') = v' := by rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [hc, smul_smul] at h1
    exact h1.symm
  · rintro ⟨a, b, ha, hb, rfl, rfl⟩
    exact (u7tv_tvGroup_smul ha hb).symm

theorem tvGroup_ne_bot {v φ : Fin ν → L} (hv : v ≠ 0) (hφ : φ ≠ 0) (h : φ ⬝ᵥ v = 0) :
    tvGroup v φ ≠ ⊥ := by
  intro hbot
  let X : SL(ν, L) := ⟨tvMat v φ 1, by rw [u7tv_det_tvMat, h, mul_zero, add_zero]⟩
  have hX : X ∈ tvGroup v φ := Subgroup.subset_closure ⟨1, rfl⟩
  have hX1 : X = 1 := Subgroup.mem_bot.mp (hbot ▸ hX)
  have hmat : tvMat v φ 1 = (1 : Matrix (Fin ν) (Fin ν) L) := by
    have := congrArg (fun Y : SL(ν, L) => (Y : Matrix (Fin ν) (Fin ν) L)) hX1
    simpa using this
  have hN : Matrix.vecMulVec v φ = 0 := by
    have h2 : (1 : Matrix (Fin ν) (Fin ν) L) + Matrix.vecMulVec v φ =
        (1 : Matrix (Fin ν) (Fin ν) L) + 0 := by
      simpa only [tvMat, one_smul, add_zero] using hmat
    simpa using add_left_cancel h2
  rw [Matrix.vecMulVec_eq_zero] at hN
  exact hN.elim hv hφ

end CFSG.StandardType.LieKnownR2.ExcPos.ExcU7
