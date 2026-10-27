module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

open CFSG.LieType.SteinbergBR.EvenSp

variable {K : Type} [Field K] {m : ℕ}

private noncomputable def ext3 (hm : 3 ≤ m) :
    (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) →* (Fin m → GL (Fin 2) K) where
  toFun a k := if h : (k : ℕ) < 3 then Matrix.SpecialLinearGroup.toGL (a ⟨k, h⟩) else 1
  map_one' := by
    funext k
    by_cases h : (k : ℕ) < 3 <;> simp [h]
  map_mul' a b := by
    funext k
    by_cases h : (k : ℕ) < 3 <;> simp [h]

private lemma ext3_apply (hm : 3 ≤ m) (a : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K)
    (k : Fin m) :
    ext3 (K := K) hm a k =
      if h : (k : ℕ) < 3 then Matrix.SpecialLinearGroup.toGL (a ⟨k, h⟩) else 1 := rfl

private lemma ext3_injective (hm : 3 ≤ m) : Function.Injective (ext3 (K := K) hm) := by
  intro a b h
  funext k
  have hk : ext3 (K := K) hm a (Fin.castLE hm k) =
      ext3 (K := K) hm b (Fin.castLE hm k) := congrFun h _
  have hcond : ((Fin.castLE hm k : Fin m) : ℕ) < 3 := by simpa using k.isLt
  rw [ext3_apply, ext3_apply, dif_pos hcond, dif_pos hcond] at hk
  exact Matrix.SpecialLinearGroup.toGL_injective hk

private lemma ext3_det (hm : 3 ≤ m) (a : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K)
    (j : Fin m) :
    ((ext3 (K := K) hm a j : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [ext3_apply]
  by_cases h : (j : ℕ) < 3
  · rw [dif_pos h]
    simpa using Matrix.SpecialLinearGroup.det_coe (a ⟨j, h⟩)
  · rw [dif_neg h]
    simp

private lemma planeMat_apply_inl_inl (h : Fin m → Matrix (Fin 2) (Fin 2) K) (j k : Fin m) :
    planeMat h (Sum.inl j) (Sum.inl k) = if j = k then h j 0 0 else 0 := by
  simp only [planeMat, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply]

private lemma planeMat_apply_inr_inl (h : Fin m → Matrix (Fin 2) (Fin 2) K) (j k : Fin m) :
    planeMat h (Sum.inr j) (Sum.inl k) = if j = k then h j 1 0 else 0 := by
  simp only [planeMat, Matrix.fromBlocks_apply₂₁, Matrix.diagonal_apply]

private lemma planeMat_apply_inr_inr (h : Fin m → Matrix (Fin 2) (Fin 2) K) (j k : Fin m) :
    planeMat h (Sum.inr j) (Sum.inr k) = if j = k then h j 1 1 else 0 := by
  simp only [planeMat, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]

private lemma planeMat_apply_inl (h : Fin m → Matrix (Fin 2) (Fin 2) K) {i : Fin m}
    (hi : h i = 1) (a : Fin m ⊕ Fin m) :
    planeMat h a (Sum.inl i) = if a = Sum.inl i then 1 else 0 := by
  rcases a with j | j
  · rw [planeMat_apply_inl_inl]
    by_cases hj : j = i
    · rw [if_pos hj, if_pos (by rw [hj]), hj, hi]
      simp
    · rw [if_neg hj, if_neg (fun hc => hj (Sum.inl.inj hc))]
  · rw [planeMat_apply_inr_inl]
    by_cases hj : j = i
    · rw [if_pos hj, if_neg Sum.inr_ne_inl, hj, hi]
      simp
    · rw [if_neg hj, if_neg Sum.inr_ne_inl]

private lemma planeMat_apply_inr (h : Fin m → Matrix (Fin 2) (Fin 2) K) {i : Fin m}
    (hi : h i = 1) (b : Fin m ⊕ Fin m) :
    planeMat h (Sum.inr i) b = if b = Sum.inr i then 1 else 0 := by
  rcases b with k | k
  · rw [planeMat_apply_inr_inl]
    by_cases hk : i = k
    · rw [if_pos hk, if_neg Sum.inl_ne_inr, hi]
      simp
    · rw [if_neg hk, if_neg Sum.inl_ne_inr]
  · rw [planeMat_apply_inr_inr]
    by_cases hk : i = k
    · rw [if_pos hk, if_pos (by rw [hk]), hi]
      simp
    · rw [if_neg hk, if_neg (fun hc => hk (Sum.inr.inj hc).symm)]

private lemma mul_single_apply (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (p q : Fin m ⊕ Fin m) (d : K) (a b : Fin m ⊕ Fin m) :
    (M * Matrix.single p q d) a b = M a p * (if q = b then d else 0) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single p]
  · simp [Matrix.single_apply]
  · intro k _ hk
    rw [Matrix.single_apply, if_neg (fun hc => hk hc.1.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

private lemma single_mul_apply (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (p q : Fin m ⊕ Fin m) (d : K) (a b : Fin m ⊕ Fin m) :
    (Matrix.single p q d * M) a b = (if p = a then d else 0) * M q b := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single q]
  · simp [Matrix.single_apply]
  · intro k _ hk
    rw [Matrix.single_apply, if_neg (fun hc => hk hc.2.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ q) h

private lemma planeMat_mul_single_inl_inr (h : Fin m → Matrix (Fin 2) (Fin 2) K) {i : Fin m}
    (hi : h i = 1) (d : K) :
    planeMat h * Matrix.single (Sum.inl i) (Sum.inr i) d =
      Matrix.single (Sum.inl i) (Sum.inr i) d := by
  ext a b
  rw [mul_single_apply, planeMat_apply_inl h hi a, Matrix.single_apply]
  by_cases ha : a = Sum.inl i
  · subst ha
    by_cases hb : b = Sum.inr i
    · subst hb; simp
    · simp [hb, Ne.symm hb]
  · simp [ha, Ne.symm ha]

private lemma single_inl_inr_mul_planeMat (h : Fin m → Matrix (Fin 2) (Fin 2) K) {i : Fin m}
    (hi : h i = 1) (d : K) :
    Matrix.single (Sum.inl i) (Sum.inr i) d * planeMat h =
      Matrix.single (Sum.inl i) (Sum.inr i) d := by
  ext a b
  rw [single_mul_apply, planeMat_apply_inr h hi b, Matrix.single_apply]
  by_cases ha : a = Sum.inl i
  · subst ha
    by_cases hb : b = Sum.inr i
    · subst hb; simp
    · simp [hb, Ne.symm hb]
  · simp [Ne.symm ha]

private lemma planeMat_transvection_comm (h : Fin m → Matrix (Fin 2) (Fin 2) K) {i : Fin m}
    (hi : h i = 1) (d : K) :
    planeMat h * Matrix.transvection (Sum.inl i) (Sum.inr i) d =
      Matrix.transvection (Sum.inl i) (Sum.inr i) d * planeMat h := by
  rw [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, planeMat_mul_single_inl_inr h hi d, single_inl_inr_mul_planeMat h hi d]

theorem exists_nsSpModel [CharP K 2] (hm : 4 ≤ m) :
    ∃ (Φ : (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) →* GL (Fin m ⊕ Fin m) K)
      (Y : Multiplicative K →* GL (Fin m ⊕ Fin m) K),
      Function.Injective Φ ∧ (∀ a, Φ a ∈ LargeEvenSpGroup K m) ∧
      (∀ c, Y c ∈ LargeEvenSpGroup K m) ∧
      Y (Multiplicative.ofAdd 1) ∉ LargeEvenScalars (Fin m ⊕ Fin m) K ∧
      (∀ c, Y c ^ 2 = 1) ∧ (∀ a c, Φ a * Y c = Y c * Φ a) := by
  have hm3 : 3 ≤ m := by omega
  let i₃ : Fin m := ⟨3, by omega⟩
  refine ⟨planeHom.comp (ext3 (K := K) hm3), spRootGL (K := K) i₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    refine ext3_injective hm3 (planeHom_injective ?_)
    simpa only [MonoidHom.comp_apply] using hab
  · intro a
    simpa only [MonoidHom.comp_apply] using
      planeHom_mem_statedSp (ext3 (K := K) hm3 a) (ext3_det hm3 a)
  · intro c
    exact spRootGL_mem i₃ c
  · intro hmem
    rw [largeEvenScalars_def] at hmem
    obtain ⟨c, hc⟩ := hmem
    have e := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl i₃) (Sum.inr i₃)) hc
    simp only [spRootGL_coe, toAdd_ofAdd, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at e
    rw [Matrix.diagonal_apply_ne _ Sum.inl_ne_inr, Matrix.transvection, Matrix.add_apply,
      Matrix.one_apply_ne Sum.inl_ne_inr, Matrix.single_apply_same, zero_add] at e
    exact zero_ne_one e
  · intro c
    rw [← map_pow]
    have hc2 : c ^ 2 = 1 := by
      rw [← ofAdd_toAdd c, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]
    rw [hc2, map_one]
  · intro a c
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, MonoidHom.comp_apply, planeHom_val, spRootGL_coe]
    have hthree : (fun j => ((ext3 (K := K) hm3 a j : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) i₃ = 1 := by
      show ((ext3 (K := K) hm3 a i₃ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
      rw [ext3_apply, dif_neg (by simp [i₃])]
      simp
    exact planeMat_transvection_comm (fun j => ((ext3 (K := K) hm3 a j : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) hthree (Multiplicative.toAdd c)

end TableBSymp

end CFSG.StandardType

end
