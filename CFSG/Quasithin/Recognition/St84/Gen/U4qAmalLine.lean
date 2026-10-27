module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLineDefs
public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDefs
public import CFSG.Quasithin.H13.U4ParYAmalgam

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par CFSG.QuasithinUnique

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem det_eq_of_fe_eq_zero {M : Matrix Ix Ix K} (h1 : M if1 ie1 = 0) (h2 : M if1 ie2 = 0)
    (h3 : M if2 ie1 = 0) (h4 : M if2 ie2 = 0) :
    M.det = (!![M ie1 ie1, M ie1 ie2; M ie2 ie1, M ie2 ie2] : Matrix (Fin 2) (Fin 2) K).det *
      (!![M if1 if1, M if1 if2; M if2 if1, M if2 if2] : Matrix (Fin 2) (Fin 2) K).det := by
  rw [← det_reindex_self ixEF]
  have hM : reindex ixEF ixEF M = fromBlocks !![M ie1 ie1, M ie1 ie2; M ie2 ie1, M ie2 ie2]
      !![M ie1 if1, M ie1 if2; M ie2 if1, M ie2 if2] 0
      !![M if1 if1, M if1 if2; M if2 if1, M if2 if2] := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [ixEF, h1, h2, h3, h4]
  rw [hM, det_fromBlocks_zero₂₁]

theorem mul_isQ2Mat_mul_apply {P P' Q : Matrix Ix Ix K} (hPP : P * P' = 1) (hQ : IsQ2Mat Q)
    {a b : Ix} (hab : a ≠ b) :
    (P * Q * P') a b = (P a ie1 * Q ie1 if1 + P a ie2 * Q ie2 if1) * P' if1 b +
      (P a ie1 * Q ie1 if2 + P a ie2 * Q ie2 if2) * P' if2 b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hQ
  have e := congrFun (congrFun hPP a) b
  rw [Matrix.one_apply_ne hab] at e
  simp only [Matrix.mul_apply, sum_ix] at e ⊢
  simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
  linear_combination e

@[expose] noncomputable def u4LineBlk (g : hypSU h 2 0) : Matrix (Fin 2) (Fin 2) K :=
  !![((g : GL Ix K) : Matrix Ix Ix K) ie1 if1, ((g : GL Ix K) : Matrix Ix Ix K) ie1 if2;
    ((g : GL Ix K) : Matrix Ix Ix K) ie2 if1, ((g : GL Ix K) : Matrix Ix Ix K) ie2 if2]

theorem u4LineBlk_apply (g : hypSU h 2 0) (i j : Fin 2) :
    u4LineBlk h g i j = ((g : GL Ix K) : Matrix Ix Ix K) (![ie1, ie2] i) (![if1, if2] j) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem u4LineBlk_mem_u4Herm {q : hypSU h 2 0} (hq : q ∈ radQ2 h) : u4LineBlk h q ∈ u4Herm h := by
  haveI := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hq
  have hgram := (mem_gramSU.mp q.2).1
  have entry : ∀ i j, ∑ k, h.bar (((q : GL Ix K) : Matrix Ix Ix K) (hypPartner k) i) *
      ((q : GL Ix K) : Matrix Ix Ix K) k j = hypGram 2 0 K i j := by
    intro i j
    have := congrFun (congrFun hgram i) j
    rw [Matrix.mul_apply] at this
    simpa only [mul_hypGram_apply, transpose_apply, map_apply] using this
  have e11 := entry if1 if1
  have e12 := entry if1 if2
  have e21 := entry if2 if1
  have e22 := entry if2 if2
  rw [sum_ix, hypGram_apply] at e11 e12 e21 e22
  simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12] at e11 e12 e21 e22
  rw [mem_u4Herm]
  intro i j
  fin_cases i <;> fin_cases j
  · show h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie1 if1) = ((q : GL Ix K) : Matrix Ix Ix K) ie1 if1
    linear_combination e11 - ((q : GL Ix K) : Matrix Ix Ix K) ie1 if1 * h2
  · show h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie1 if2) = ((q : GL Ix K) : Matrix Ix Ix K) ie2 if1
    linear_combination e21 - ((q : GL Ix K) : Matrix Ix Ix K) ie2 if1 * h2
  · show h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie2 if1) = ((q : GL Ix K) : Matrix Ix Ix K) ie1 if2
    linear_combination e12 - ((q : GL Ix K) : Matrix Ix Ix K) ie1 if2 * h2
  · show h.bar (((q : GL Ix K) : Matrix Ix Ix K) ie2 if2) = ((q : GL Ix K) : Matrix Ix Ix K) ie2 if2
    linear_combination e22 - ((q : GL Ix K) : Matrix Ix Ix K) ie2 if2 * h2

theorem u4LineBlk_one : u4LineBlk h (1 : hypSU h 2 0) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4LineBlk]

theorem u4LineBlk_mul {q q' : hypSU h 2 0} (hq : q ∈ radQ2 h) (hq' : q' ∈ radQ2 h) :
    u4LineBlk h (q * q') = u4LineBlk h q + u4LineBlk h q' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hq
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := hq'
  ext i j
  rw [Matrix.add_apply, u4LineBlk_apply, u4LineBlk_apply, u4LineBlk_apply, coe_mul_hypSU,
    Matrix.mul_apply, sum_ix]
  fin_cases i <;> fin_cases j <;>
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, b1, b2, b3, b4, b5, b6, b7, b8, b9,
      b10, b11, b12] <;> ring

theorem u4LineBlk_inj {q q' : hypSU h 2 0} (hq : q ∈ radQ2 h) (hq' : q' ∈ radQ2 h)
    (he : u4LineBlk h q = u4LineBlk h q') : q = q' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hq
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := hq'
  have e00 : ((q : GL Ix K) : Matrix Ix Ix K) ie1 if1 = ((q' : GL Ix K) : Matrix Ix Ix K) ie1 if1 :=
    congrFun (congrFun he 0) 0
  have e01 : ((q : GL Ix K) : Matrix Ix Ix K) ie1 if2 = ((q' : GL Ix K) : Matrix Ix Ix K) ie1 if2 :=
    congrFun (congrFun he 0) 1
  have e10 : ((q : GL Ix K) : Matrix Ix Ix K) ie2 if1 = ((q' : GL Ix K) : Matrix Ix Ix K) ie2 if1 :=
    congrFun (congrFun he 1) 0
  have e11 : ((q : GL Ix K) : Matrix Ix Ix K) ie2 if2 = ((q' : GL Ix K) : Matrix Ix Ix K) ie2 if2 :=
    congrFun (congrFun he 1) 1
  apply hypSU_ext h
  ext a b
  rcases ix_cases a with rfl | rfl | rfl | rfl <;> rcases ix_cases b with rfl | rfl | rfl | rfl <;>
    simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, b1, b2, b3, b4, b5, b6, b7, b8,
      b9, b10, b11, b12, e00, e01, e10, e11]

@[expose] noncomputable def u4Q2Mat (X : Matrix (Fin 2) (Fin 2) K) : Matrix Ix Ix K :=
  1 + single ie1 if1 (X 0 0) + single ie1 if2 (X 0 1) + single ie2 if1 (X 1 0) +
    single ie2 if2 (X 1 1)

theorem u4Q2Mat_apply (X : Matrix (Fin 2) (Fin 2) K) (i j : Ix) :
    u4Q2Mat X i j = (1 : Matrix Ix Ix K) i j + (if ie1 = i ∧ if1 = j then X 0 0 else 0) +
      (if ie1 = i ∧ if2 = j then X 0 1 else 0) + (if ie2 = i ∧ if1 = j then X 1 0 else 0) +
      (if ie2 = i ∧ if2 = j then X 1 1 else 0) := by
  simp only [u4Q2Mat, Matrix.add_apply, Matrix.single_apply]

include h in
theorem u4Q2Mat_mul_self (X : Matrix (Fin 2) (Fin 2) K) : u4Q2Mat X * u4Q2Mat X = 1 := by
  haveI := h.charP
  ext i j
  rw [Matrix.mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [u4Q2Mat_apply, one_apply, CharTwo.add_self_eq_zero]

theorem u4Q2Mat_gram {X : Matrix (Fin 2) (Fin 2) K} (hX : X ∈ u4Herm h) :
    ((u4Q2Mat X).map h.bar)ᵀ * hypGram 2 0 K * u4Q2Mat X = hypGram 2 0 K := by
  haveI := h.charP
  have hXe := (mem_u4Herm h).mp hX
  ext i j
  rw [Matrix.mul_apply, sum_ix]
  simp only [mul_hypGram_apply, transpose_apply, map_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [u4Q2Mat_apply, one_apply, hypGram_apply, hXe, CharTwo.add_self_eq_zero]

theorem det_u4Q2Mat (X : Matrix (Fin 2) (Fin 2) K) : (u4Q2Mat X).det = 1 := by
  rw [det_eq_of_fe_eq_zero (by simp [u4Q2Mat_apply]) (by simp [u4Q2Mat_apply])
    (by simp [u4Q2Mat_apply]) (by simp [u4Q2Mat_apply])]
  simp [u4Q2Mat_apply, Matrix.det_fin_two_of]

@[expose] noncomputable def u4Q2Elt (X : ↥(u4Herm h)) : hypSU h 2 0 :=
  ⟨⟨u4Q2Mat (X : Matrix (Fin 2) (Fin 2) K), u4Q2Mat (X : Matrix (Fin 2) (Fin 2) K),
    u4Q2Mat_mul_self h _, u4Q2Mat_mul_self h _⟩,
    mem_gramSU.mpr ⟨u4Q2Mat_gram h X.2, det_u4Q2Mat _⟩⟩

theorem coe_u4Q2Elt (X : ↥(u4Herm h)) :
    (((u4Q2Elt h X : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      u4Q2Mat (X : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem u4Q2Elt_mem_radQ2 (X : ↥(u4Herm h)) : u4Q2Elt h X ∈ radQ2 h := by
  change IsQ2Mat (u4Q2Mat (X : Matrix (Fin 2) (Fin 2) K))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [u4Q2Mat_apply, one_apply]

theorem u4LineBlk_u4Q2Elt (X : ↥(u4Herm h)) :
    u4LineBlk h (u4Q2Elt h X) = (X : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  rw [u4LineBlk_apply, coe_u4Q2Elt, u4Q2Mat_apply]
  fin_cases i <;> fin_cases j <;> simp [one_apply]

@[expose] noncomputable def u4RadQ2CoordHom :
    ↥(radQ2 h) →* Multiplicative (Fin 4 → h.fixedField) where
  toFun q := Multiplicative.ofAdd (u4HermCoord h ⟨u4LineBlk h q, u4LineBlk_mem_u4Herm h q.2⟩)
  map_one' := by
    rw [← ofAdd_zero, ← (u4HermCoord h).map_zero]
    exact congrArg (fun X => Multiplicative.ofAdd (u4HermCoord h X))
      (Subtype.ext (u4LineBlk_one h))
  map_mul' q q' := by
    rw [← ofAdd_add, ← (u4HermCoord h).map_add]
    exact congrArg (fun X => Multiplicative.ofAdd (u4HermCoord h X))
      (Subtype.ext (u4LineBlk_mul h q.2 q'.2))

theorem u4RadQ2CoordHom_injective : Function.Injective (u4RadQ2CoordHom h) := by
  intro q q' he
  have h1 := (u4HermCoord h).injective (Multiplicative.ofAdd.injective he)
  exact Subtype.ext (u4LineBlk_inj h q.2 q'.2 (congrArg Subtype.val h1))

theorem u4RadQ2CoordHom_surjective : Function.Surjective (u4RadQ2CoordHom h) := by
  intro v
  obtain ⟨X, hX⟩ := (u4HermCoord h).surjective (Multiplicative.toAdd v)
  refine ⟨⟨u4Q2Elt h X, u4Q2Elt_mem_radQ2 h X⟩, ?_⟩
  have hb : (⟨u4LineBlk h (u4Q2Elt h X), u4LineBlk_mem_u4Herm h (u4Q2Elt_mem_radQ2 h X)⟩ :
      ↥(u4Herm h)) = X :=
    Subtype.ext (u4LineBlk_u4Q2Elt h X)
  change Multiplicative.ofAdd (u4HermCoord h ⟨u4LineBlk h (u4Q2Elt h X),
    u4LineBlk_mem_u4Herm h (u4Q2Elt_mem_radQ2 h X)⟩) = v
  rw [hb, hX]
  rfl

@[expose] noncomputable def u4RadQ2Coord : ↥(radQ2 h) ≃* Multiplicative (Fin 4 → h.fixedField) :=
  MulEquiv.ofBijective (u4RadQ2CoordHom h)
    ⟨u4RadQ2CoordHom_injective h, u4RadQ2CoordHom_surjective h⟩

theorem toAdd_u4RadQ2Coord (q : ↥(radQ2 h)) :
    Multiplicative.toAdd (u4RadQ2Coord h q) =
      u4HermCoord h ⟨u4LineBlk h q, u4LineBlk_mem_u4Herm h q.2⟩ :=
  rfl

theorem u4LineBlk_conj (p : hypSU h 2 0) {q : hypSU h 2 0} (hq : q ∈ radQ2 h) :
    u4LineBlk h (p * q * p⁻¹) = rho2 h p * u4LineBlk h q * ((rho2 h p).map h.bar)ᵀ := by
  have hPP : ((p : GL Ix K) : Matrix Ix Ix K) *
      (((p⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = 1 := by
    rw [← coe_mul_hypSU, mul_inv_cancel]
    rfl
  have hQ : IsQ2Mat ((q : GL Ix K) : Matrix Ix Ix K) := hq
  ext i j
  have hij : (![ie1, ie2] i : Ix) ≠ ![if1, if2] j := by
    fin_cases i <;> fin_cases j <;> simp
  rw [u4LineBlk_apply, coe_mul_hypSU, coe_mul_hypSU, mul_isQ2Mat_mul_apply hPP hQ hij,
    inv_apply h p, inv_apply h p]
  fin_cases i <;> fin_cases j <;>
    simp [rho2, u4LineBlk, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[expose] noncomputable def u4FFBlk (g : hypSU h 2 0) : Matrix (Fin 2) (Fin 2) K :=
  !![((g : GL Ix K) : Matrix Ix Ix K) if1 if1, ((g : GL Ix K) : Matrix Ix Ix K) if1 if2;
    ((g : GL Ix K) : Matrix Ix Ix K) if2 if1, ((g : GL Ix K) : Matrix Ix Ix K) if2 if2]

theorem rho2_map_transpose_mul_u4FFBlk {p : hypSU h 2 0} (hp : p ∈ parP2 h) :
    ((rho2 h p).map h.bar)ᵀ * u4FFBlk h p = 1 := by
  obtain ⟨c1, c2, c3, c4⟩ := (mem_parP2_iff h p).mp hp
  have hgram := (mem_gramSU.mp p.2).1
  have entry : ∀ i j, ∑ k, h.bar (((p : GL Ix K) : Matrix Ix Ix K) (hypPartner k) i) *
      ((p : GL Ix K) : Matrix Ix Ix K) k j = hypGram 2 0 K i j := by
    intro i j
    have := congrFun (congrFun hgram i) j
    rw [Matrix.mul_apply] at this
    simpa only [mul_hypGram_apply, transpose_apply, map_apply] using this
  have e11 := entry ie1 if1
  have e12 := entry ie1 if2
  have e21 := entry ie2 if1
  have e22 := entry ie2 if2
  rw [sum_ix, hypGram_apply] at e11 e12 e21 e22
  simp [c1, c2, c3, c4] at e11 e12 e21 e22
  ext i j
  fin_cases i <;> fin_cases j
  · simp [rho2, u4FFBlk, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination e11
  · simp [rho2, u4FFBlk, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination e12
  · simp [rho2, u4FFBlk, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination e21
  · simp [rho2, u4FFBlk, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination e22

theorem det_eq_rho2_mul_u4FFBlk {p : hypSU h 2 0} (hp : p ∈ parP2 h) :
    ((p : GL Ix K) : Matrix Ix Ix K).det = (rho2 h p).det * (u4FFBlk h p).det := by
  obtain ⟨c1, c2, c3, c4⟩ := (mem_parP2_iff h p).mp hp
  exact det_eq_of_fe_eq_zero c1 c2 c3 c4

theorem rho2_det_of_mem_parP2 {p : hypSU h 2 0} (hp : p ∈ parP2 h) :
    h.bar (rho2 h p).det = (rho2 h p).det := by
  have hdet : (rho2 h p).det * (u4FFBlk h p).det = 1 := by
    rw [← det_eq_rho2_mul_u4FFBlk h hp]
    exact (mem_gramSU.mp p.2).2
  have hbar : h.bar (rho2 h p).det * (u4FFBlk h p).det = 1 := by
    have e := congrArg Matrix.det (rho2_map_transpose_mul_u4FFBlk h hp)
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at e
    rw [RingHom.map_det]
    exact e
  have hD : (u4FFBlk h p).det ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  exact mul_right_cancel₀ hD (hbar.trans hdet.symm)

@[expose] noncomputable def u4Rho2GL {p : hypSU h 2 0} (hp : p ∈ parP2 h) : GL (Fin 2) K :=
  ⟨rho2 h p, rho2 h p⁻¹,
    by rw [← rho2_mul h ((parP2 h).inv_mem hp), mul_inv_cancel, rho2_one],
    by rw [← rho2_mul h hp, inv_mul_cancel, rho2_one]⟩

theorem u4Rho2GL_mem {p : hypSU h 2 0} (hp : p ∈ parP2 h) : u4Rho2GL h hp ∈ u4DetFixGL h :=
  rho2_det_of_mem_parP2 h hp

private theorem rho2_eq_one_of_mem_radQ2' {g : hypSU h 2 0} (hg : g ∈ radQ2 h) : rho2 h g = 1 := by
  obtain ⟨a1, a2, a3, a4, -⟩ := hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho2, a1, a2, a3, a4]

@[expose] def u4LeviMat (A D : Matrix (Fin 2) (Fin 2) K) : Matrix Ix Ix K :=
  (fromBlocks A 0 0 D).submatrix ixEF ixEF

theorem u4LeviMat_mul (A D A' D' : Matrix (Fin 2) (Fin 2) K) :
    u4LeviMat A D * u4LeviMat A' D' = u4LeviMat (A * A') (D * D') := by
  rw [u4LeviMat, u4LeviMat, Matrix.submatrix_mul_equiv, fromBlocks_multiply, u4LeviMat]
  simp

theorem u4LeviMat_one : u4LeviMat (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  rw [u4LeviMat, fromBlocks_one, Matrix.submatrix_one_equiv]

theorem det_u4LeviMat (A D : Matrix (Fin 2) (Fin 2) K) :
    (u4LeviMat A D).det = A.det * D.det := by
  rw [u4LeviMat, Matrix.det_submatrix_equiv_self, det_fromBlocks_zero₂₁]

private theorem hypGram_eq_submatrix :
    hypGram 2 0 K = (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix
      ixEF ixEF := by
  ext a b
  rcases ix_cases a with rfl | rfl | rfl | rfl <;> rcases ix_cases b with rfl | rfl | rfl | rfl <;>
    simp [hypGram_apply, ixEF, one_apply]

theorem u4LeviMat_gram {A D : Matrix (Fin 2) (Fin 2) K} (hAD : (A.map h.bar)ᵀ * D = 1)
    (hDA : (D.map h.bar)ᵀ * A = 1) :
    ((u4LeviMat A D).map h.bar)ᵀ * hypGram 2 0 K * u4LeviMat A D = hypGram 2 0 K := by
  have hM : ((u4LeviMat A D).map h.bar)ᵀ =
      (fromBlocks (A.map h.bar)ᵀ 0 0 (D.map h.bar)ᵀ).submatrix ixEF ixEF := by
    rw [u4LeviMat, ← Matrix.submatrix_map, Matrix.transpose_submatrix, fromBlocks_map,
      fromBlocks_transpose]
    simp
  rw [hM, hypGram_eq_submatrix, u4LeviMat, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, fromBlocks_multiply, fromBlocks_multiply]
  simp [hAD, hDA]

@[expose] noncomputable def u4LeviMatHom : GL (Fin 2) K →* Matrix Ix Ix K where
  toFun A := u4LeviMat (A : Matrix (Fin 2) (Fin 2) K)
    ((((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ
  map_one' := by
    simp only [inv_one, Matrix.GeneralLinearGroup.coe_one]
    rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one, u4LeviMat_one]
  map_mul' A B := by
    simp only [_root_.mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul]
    rw [u4LeviMat_mul, Matrix.map_mul, Matrix.transpose_mul]

theorem u4LeviMatHom_mem {A : GL (Fin 2) K} (hA : A ∈ u4DetFixGL h) :
    (u4LeviMatHom h).toHomUnits A ∈ hypSU h 2 0 := by
  have hbb : ∀ M : Matrix (Fin 2) (Fin 2) K, (M.map h.bar).map h.bar = M := by
    intro M
    ext i j
    simp [h.bar_bar]
  have hinv : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · change ((u4LeviMat (A : Matrix (Fin 2) (Fin 2) K)
        ((((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ).map h.bar)ᵀ *
        hypGram 2 0 K * u4LeviMat (A : Matrix (Fin 2) (Fin 2) K)
        ((((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ = hypGram 2 0 K
    refine u4LeviMat_gram h ?_ ?_
    · rw [← Matrix.transpose_mul, ← Matrix.map_mul, hinv,
        Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one]
    · rw [Matrix.transpose_map, Matrix.transpose_transpose, hbb, hinv]
  · change (u4LeviMat (A : Matrix (Fin 2) (Fin 2) K)
        ((((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ).det = 1
    have e1 : h.bar ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
        ((((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map h.bar).det :=
      RingHom.map_det _ _
    have e2 : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
        (A : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [← Matrix.det_mul, hinv, Matrix.det_one]
    rw [det_u4LeviMat, Matrix.det_transpose, ← e1, eq_inv_of_mul_eq_one_left e2, map_inv₀,
      (mem_u4DetFixGL h).mp hA]
    exact mul_inv_cancel₀ (right_ne_zero_of_mul_eq_one e2)

@[expose] noncomputable def u4LeviHom : ↥(u4DetFixGL h) →* hypSU h 2 0 :=
  ((u4LeviMatHom h).toHomUnits.comp (u4DetFixGL h).subtype).codRestrict (hypSU h 2 0)
    fun A => u4LeviMatHom_mem h A.2

theorem coe_u4LeviHom (A : ↥(u4DetFixGL h)) :
    (((u4LeviHom h A : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      u4LeviMat ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        (((((A : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ :=
  rfl

theorem rho2_u4LeviHom (A : ↥(u4DetFixGL h)) :
    rho2 h (u4LeviHom h A) = ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho2, coe_u4LeviHom, u4LeviMat, ixEF]

theorem u4LeviHom_mem_parP2 (A : ↥(u4DetFixGL h)) : u4LeviHom h A ∈ parP2 h := by
  rw [mem_parP2_iff, coe_u4LeviHom]
  simp [u4LeviMat, ixEF]

theorem range_u4LeviHom_le_parP2 : (u4LeviHom h).range ≤ parP2 h := by
  rintro _ ⟨A, rfl⟩
  exact u4LeviHom_mem_parP2 h A

theorem range_u4LeviHom_inf_radQ2 : (u4LeviHom h).range ⊓ radQ2 h = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgL, hgQ⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hgL
  rw [Subgroup.mem_bot]
  have h1 : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← rho2_u4LeviHom h A]
    exact rho2_eq_one_of_mem_radQ2' h hgQ
  have hA : A = 1 := Subtype.ext (Units.ext h1)
  rw [hA, map_one]

theorem radQ2_sup_range_u4LeviHom : radQ2 h ⊔ (u4LeviHom h).range = parP2 h := by
  refine le_antisymm (sup_le (radQ2_le_parP2 h) (range_u4LeviHom_le_parP2 h)) ?_
  intro g hg
  obtain ⟨A, hA⟩ : ∃ A : ↥(u4DetFixGL h), (A : GL (Fin 2) K) = u4Rho2GL h hg :=
    ⟨⟨_, u4Rho2GL_mem h hg⟩, rfl⟩
  have hl : u4LeviHom h A ∈ parP2 h := u4LeviHom_mem_parP2 h A
  have hq : g * (u4LeviHom h A)⁻¹ ∈ radQ2 h := by
    refine mem_radQ2_of_rho2 h ((parP2 h).mul_mem hg ((parP2 h).inv_mem hl)) ?_
    rw [rho2_mul h ((parP2 h).inv_mem hl), ← map_inv, rho2_u4LeviHom, Subgroup.coe_inv, hA]
    exact Units.mul_inv (u4Rho2GL h hg)
  have e : g = g * (u4LeviHom h A)⁻¹ * u4LeviHom h A := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right ⟨A, rfl⟩)

theorem parP2_inf_centralizer_radQ2_le :
    parP2 h ⊓ Subgroup.centralizer (radQ2 h : Set (hypSU h 2 0)) ≤ radQ2 h := by
  intro g hg
  obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.mp hg
  refine mem_radQ2_of_rho2 h hgP ?_
  refine eq_one_of_forall_twist_eq h (rho2_det_of_mem_parP2 h hgP) fun X hX => ?_
  have hq : u4Q2Elt h ⟨X, hX⟩ ∈ radQ2 h := u4Q2Elt_mem_radQ2 h _
  have hcomm : u4Q2Elt h ⟨X, hX⟩ * g = g * u4Q2Elt h ⟨X, hX⟩ :=
    Subgroup.mem_centralizer_iff.mp hgC _ hq
  have hconj : g * u4Q2Elt h ⟨X, hX⟩ * g⁻¹ = u4Q2Elt h ⟨X, hX⟩ := by
    rw [← hcomm, mul_inv_cancel_right]
  have h1 := u4LineBlk_conj h g hq
  rw [hconj, u4LineBlk_u4Q2Elt] at h1
  exact h1.symm

theorem actsByMatrix_u4RadQ2Coord (p : hypSU h 2 0) (A : GL (Fin 2) K)
    (hpA : rho2 h p = (A : Matrix (Fin 2) (Fin 2) K)) :
    ActsByMatrix (u4RadQ2Coord h) p
      ((u4TwistHom h A : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField) := by
  intro x y hxy
  rw [toAdd_u4RadQ2Coord, toAdd_u4RadQ2Coord, coe_u4TwistHom, u4TwistMat_mulVec]
  congr 1
  apply Subtype.ext
  rw [coe_u4TwistLin]
  change u4LineBlk h (y : hypSU h 2 0) = (A : Matrix (Fin 2) (Fin 2) K) *
    u4LineBlk h (x : hypSU h 2 0) * ((A : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ
  rw [hxy, u4LineBlk_conj h p x.2, hpA]

theorem linAction_parP2 : LinAction (parP2 h) (radQ2 h) (u4Gamma2 h) := by
  refine ⟨u4RadQ2Coord h, ?_, ?_⟩
  · intro p hp
    exact ⟨u4TwistHom h (u4Rho2GL h hp), u4TwistHom_mem_u4Gamma2 h (u4Rho2GL_mem h hp),
      actsByMatrix_u4RadQ2Coord h p _ rfl⟩
  · intro M hM
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hM
    exact ⟨u4LeviHom h ⟨A, hA⟩, u4LeviHom_mem_parP2 h _,
      actsByMatrix_u4RadQ2Coord h _ A (rho2_u4LeviHom h _)⟩

theorem isLinSemidirect_parP2 : IsLinSemidirect (parP2 h) (radQ2 h) (u4Gamma2 h) where
  le := radQ2_le_parP2 h
  normal := parP2_le_normalizer_radQ2 h
  cent := parP2_inf_centralizer_radQ2_le h
  split := ⟨(u4LeviHom h).range, range_u4LeviHom_le_parP2 h, range_u4LeviHom_inf_radQ2 h,
    radQ2_sup_range_u4LeviHom h⟩
  act := linAction_parP2 h

theorem isSylowTwoOf_hypUnitriangular_parP2 :
    IsSylowTwoOf (hypUnitriangular h 2 0) (parP2 h) := by
  have hT := isSylowTwoOf_hypUnitriangular h
  have hle : hypUnitriangular h 2 0 ≤ parP2 h :=
    (hypUnitriangular_le_parH2 h).trans (parH2_le_parP2 h)
  refine ⟨hle, hT.2.1, fun h2 => hT.2.2 ?_⟩
  change 2 ∣ (hypUnitriangular h 2 0).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact h2.trans (Subgroup.relIndex_dvd_index_of_le hle)

end CFSG.Quasithin.F112R.St84

end
