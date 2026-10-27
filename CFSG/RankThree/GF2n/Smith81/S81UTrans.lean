module

public import CFSG.RankThree.GF2n.Smith81.S81UFrame
public import CFSG.RankThree.GF2n.Smith81.S81UModelDef

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

@[expose] def hermMat (σ : F ≃+* F) (a v : Fin 3 → Fin 6 → F) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun i j => ∑ k, a i k * σ (v j k)

private theorem h44_det_map (P : Matrix (Fin 3) (Fin 3) F) : (P.map σ).det = σ P.det := by
  rw [RingEquiv.map_det, RingEquiv.mapMatrix_apply]

private theorem h44_det_entries (v : Fin 3 → Fin 6 → F) (I : Set.powersetCard (Fin 6) 3) :
    (Matrix.of fun i j : Fin 3 => σ (v j (enum I i))).det = σ (coord F (ιMulti F 3 v) I) := by
  rw [coord_ιMulti, ← Matrix.det_transpose (Matrix.of fun i j : Fin 3 => v i (enum I j)),
    ← h44_det_map]
  congr 1

theorem sum_coord_mul_sigma_coord (a v : Fin 3 → Fin 6 → F) :
    ∑ I, coord F (ιMulti F 3 a) I * σ (coord F (ιMulti F 3 v) I) = (hermMat σ a v).det := by
  have key : (cubeBasis F).constr F (fun I => σ (coord F (ιMulti F 3 v) I)) =
      exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap
        (Matrix.mulVecLin (Matrix.of fun (j : Fin 3) (k : Fin 6) => σ (v j k)))) := by
    refine (cubeBasis F).ext fun I => ?_
    simp only [Module.Basis.constr_basis]
    rw [cubeBasis_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      AlternatingMap.compLinearMap_apply, ← h44_det_entries v I]
    show Matrix.detRowAlternating _ = Matrix.detRowAlternating _
    congr 1
    funext i j
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, e, Pi.single_apply]
  have hR : exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap
      (Matrix.mulVecLin (Matrix.of fun (j : Fin 3) (k : Fin 6) => σ (v j k)))) (ιMulti F 3 a) =
      (hermMat σ a v).det := by
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply]
    show Matrix.detRowAlternating _ = Matrix.detRowAlternating _
    congr 1
    funext i j
    simp [hermMat, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, mul_comm]
  have hL : ∑ I, coord F (ιMulti F 3 a) I * σ (coord F (ιMulti F 3 v) I) =
      (cubeBasis F).constr F (fun I => σ (coord F (ιMulti F 3 v) I)) (ιMulti F 3 a) := by
    simp [Module.Basis.constr_apply_fintype, coord]
  exact hL.trans ((DFunLike.congr_fun key _).trans hR)

theorem exists_beta_formula : ∃ t : F, t ≠ 0 ∧ ∀ η ξ : Cube F,
    beta F η ξ = t * ∑ I, coord F η I * coord F ξ (cmpl I) := by
  obtain ⟨t, ht, hb⟩ := bmat_eq_smul_Pm (K := F)
  refine ⟨t, ht, fun η ξ => ?_⟩
  have hPm : ∀ a b : Idx, bmat (K := F) a b = if b = cmpl a then t else 0 := by
    intro a b
    rw [hb]
    by_cases h : b = cmpl a <;> simp [Pm, h]
  rw [beta_expand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (cmpl a)]
  · rw [hPm, if_pos rfl]
    ring
  · intro b _ hb'
    simp [hPm, hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] def hermL (σ : F ≃+* F) (v : Fin 3 → Fin 6 → F) : (Fin 6 → F) →ₗ[F] (Fin 3 → F) where
  toFun x j := ∑ k, σ (v j k) * x k
  map_add' x y := by
    funext j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext j
    simp [Finset.mul_sum, mul_left_comm]

theorem hermL_surjective {v : Fin 3 → Fin 6 → F} (hv : ιMulti F 3 v ≠ 0) :
    Function.Surjective (hermL σ v) := by
  obtain ⟨I, hI⟩ : ∃ I, coord F (ιMulti F 3 v) I ≠ 0 := by
    by_contra hcon
    apply hv
    apply (cubeBasis F).ext_elem
    intro I
    rw [map_zero, Finsupp.zero_apply]
    by_contra h
    exact hcon ⟨I, h⟩
  rw [coord_ιMulti] at hI
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 3) (Fin 3) F,
      N = Matrix.of fun j l => σ (v j (enum I l)) := ⟨_, rfl⟩
  have hNdet : N.det ≠ 0 := by
    have h1 : N.det = σ (Matrix.of fun i l => v i (enum I l)).det := by
      rw [hN]
      exact (RingEquiv.map_det σ (Matrix.of fun i l => v i (enum I l))).symm
    rw [h1]
    intro h
    apply hI
    apply σ.injective
    rw [h, map_zero]
  intro r
  obtain ⟨y, hy⟩ : ∃ y : Fin 3 → F, N.mulVec y = r := by
    refine ⟨N⁻¹.mulVec r, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N (isUnit_iff_ne_zero.mpr hNdet),
      Matrix.one_mulVec]
  have hsum : ∀ j, r j = ∑ l, σ (v j (enum I l)) * y l := by
    intro j
    rw [← hy]
    subst hN
    rfl
  refine ⟨fun k => ∑ l, if enum I l = k then y l else 0, ?_⟩
  funext j
  show ∑ k, σ (v j k) * ∑ l, (if enum I l = k then y l else 0) = r j
  rw [hsum j]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [mul_ite]

private theorem h45_hermMat_apply (a v : Fin 3 → Fin 6 → F) (i j : Fin 3) :
    hermMat σ a v i j = hermL σ v (a i) j := by
  show ∑ k, a i k * σ (v j k) = ∑ k, σ (v j k) * a i k
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem hermF_eq_zero_of_theta_fixed_pure (hσ : ∀ c, σ (σ c) = c) {v : Fin 3 → Fin 6 → F}
    (hv : ιMulti F 3 v ≠ 0) (hθ : theta σ (ιMulti F 3 v) = ιMulti F 3 v) (i j : Fin 3) :
    ∑ k, σ (v i k) * v j k = 0 := by
  have hcoord : ∀ I, coord F (ιMulti F 3 v) (cmpl I) = σ (coord F (ιMulti F 3 v) I) := by
    intro I
    have h := coord_theta (σ := σ) (ιMulti F 3 v) I
    rw [hθ] at h
    exact h
  obtain ⟨t, ht, hβ⟩ := exists_beta_formula (F := F)
  have hA : ∀ a : Fin 3 → Fin 6 → F,
      t * (hermMat σ a v).det = (Matrix.of (Fin.append a v)).det := by
    intro a
    rw [← sum_coord_mul_sigma_coord (σ := σ) a v, ← beta_ιMulti a v, hβ]
    simp only [hcoord]
  have hdet0 : ∀ (p : Fin 3) (y z : Fin 6 → F), (hermMat σ ![v p, y, z] v).det = 0 := by
    intro p y z
    have hz : (Matrix.of (Fin.append ![v p, y, z] v)).det = 0 := by
      apply Matrix.det_zero_of_row_eq (i := Fin.castAdd 3 (0 : Fin 3))
        (j := Fin.natAdd 3 p)
      · intro h
        have h' := congrArg Fin.val h
        simp only [Fin.coe_castAdd, Fin.val_zero, Fin.coe_natAdd] at h'
        omega
      · funext k
        simp only [Matrix.of_apply, Fin.append_left, Fin.append_right, Matrix.cons_val_zero]
    rcases mul_eq_zero.mp ((hA ![v p, y, z]).trans hz) with h | h
    · exact absurd h ht
    · exact h
  have hrow : ∀ p u : Fin 3, ∑ k, v p k * σ (v u k) = 0 := by
    intro p
    have hsol : ∀ q : Fin 3, ∃ y : Fin 6 → F, hermL σ v y = Pi.single q 1 := fun q =>
      hermL_surjective hv (Pi.single q 1)
    obtain ⟨y0, hy0⟩ := hsol 0
    obtain ⟨y1, hy1⟩ := hsol 1
    obtain ⟨y2, hy2⟩ := hsol 2
    have hd01 := hdet0 p y1 y2
    have hd02 := hdet0 p y0 y2
    have hd12 := hdet0 p y0 y1
    rw [Matrix.det_fin_three] at hd01 hd02 hd12
    simp [h45_hermMat_apply, hy0, hy1, hy2, Pi.single_apply, Matrix.cons_val_two,
      Matrix.tail_cons] at hd01 hd02 hd12
    have hu : ∀ u : Fin 3, hermL σ v (v p) u = 0 := by
      intro u
      fin_cases u
      · simpa using hd01
      · simpa using hd02
      · simpa using hd12
    intro u
    calc ∑ k, v p k * σ (v u k) = ∑ k, σ (v u k) * v p k :=
          Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = hermL σ v (v p) u := rfl
      _ = 0 := hu u
  have hfin : ∑ k, σ (v i k) * v j k = σ (∑ k, v i k * σ (v j k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hσ]
  rw [hfin, hrow i j, map_zero]

private theorem h46_right_sum (x : Fin 6 → F) (a : Fin 3 → F) (u : Fin 3 → Fin 6 → F) :
    ∑ k, σ (x k) * ∑ l, a l * u l k = ∑ l, a l * ∑ k, σ (x k) * u l k := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem h46_right_add (x y z : Fin 6 → F) :
    ∑ k, σ (x k) * (y k + z k) = ∑ k, σ (x k) * y k + ∑ k, σ (x k) * z k := by
  simp only [mul_add, Finset.sum_add_distrib]

private theorem h46_left_sum (x : Fin 6 → F) (a : Fin 3 → F) (u : Fin 3 → Fin 6 → F)
    (y : Fin 6 → F) :
    ∑ k, σ (x k + ∑ l, a l * u l k) * y k =
      ∑ k, σ (x k) * y k + ∑ l, σ (a l) * ∑ k, σ (u l k) * y k := by
  simp only [map_add, map_sum, map_mul, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem h46_sigma_herm (hinv : ∀ c, σ (σ c) = c) (x y : Fin 6 → F) :
    σ (∑ k, σ (x k) * y k) = ∑ k, σ (y k) * x k := by
  simp only [map_sum, map_mul, hinv]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem exists_hyperbolic_partners (hσ : IsUnitaryInvolution σ) {v : Fin 3 → Fin 6 → F}
    (hv : ιMulti F 3 v ≠ 0) (hiso : ∀ i j, ∑ k, σ (v i k) * v j k = 0) :
    ∃ w : Fin 3 → Fin 6 → F, (∀ i j, ∑ k, σ (v i k) * w j k = if i = j then 1 else 0) ∧
      ∀ i j, ∑ k, σ (w i k) * w j k = 0 := by
  choose w0 hw0 using fun j : Fin 3 => hermL_surjective (σ := σ) hv (Pi.single j (1 : F))
  have hd : ∀ j i : Fin 3, ∑ k, σ (v i k) * w0 j k = if i = j then 1 else 0 := by
    intro j i
    have h := congrFun (hw0 j) i
    rw [Pi.single_apply] at h
    exact h
  have hd' : ∀ j i : Fin 3, ∑ k, σ (w0 j k) * v i k = if i = j then 1 else 0 := by
    intro j i
    rw [← h46_sigma_herm hσ.invol (v i) (w0 j), hd j i]
    split_ifs <;> simp
  have hgs : ∀ i j : Fin 3, σ (∑ k, σ (w0 i k) * w0 j k) = ∑ k, σ (w0 j k) * w0 i k :=
    fun i j => h46_sigma_herm hσ.invol (w0 i) (w0 j)
  choose τ hτ using fun i : Fin 3 => hσ.trace_surj _ (hgs i i)
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → Fin 3 → F, ∀ j l : Fin 3,
      c j l = if l < j then ∑ k, σ (w0 l k) * w0 j k else if l = j then τ j else 0 :=
    ⟨fun j l => if l < j then ∑ k, σ (w0 l k) * w0 j k else if l = j then τ j else 0,
      fun _ _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → Fin 6 → F, ∀ j k, w j k = w0 j k + ∑ l, c j l * v l k :=
    ⟨fun j k => w0 j k + ∑ l, c j l * v l k, fun _ _ => rfl⟩
  have hA : ∀ j l : Fin 3,
      ∑ k, σ (v l k) * (w0 j k + ∑ m, c j m * v m k) = if l = j then 1 else 0 := by
    intro j l
    rw [h46_right_add, h46_right_sum]
    simp only [hiso, mul_zero, Finset.sum_const_zero, add_zero]
    exact hd j l
  have hB : ∀ i j : Fin 3,
      ∑ k, σ (w0 i k) * (w0 j k + ∑ m, c j m * v m k) = (∑ k, σ (w0 i k) * w0 j k) + c j i := by
    intro i j
    rw [h46_right_add, h46_right_sum]
    simp [hd', mul_ite]
  have hC : ∀ i j : Fin 3,
      ∑ l, σ (c i l) * ∑ k, σ (v l k) * (w0 j k + ∑ m, c j m * v m k) = σ (c i j) := by
    intro i j
    simp [hA, mul_ite]
  refine ⟨w, fun i j => ?_, fun i j => ?_⟩
  · simp only [hw]
    exact hA j i
  · simp only [hw]
    rw [h46_left_sum, hB i j, hC i j]
    rcases lt_trichotomy i j with h | h | h
    · rw [hc j i, if_pos h, hc i j, if_neg (lt_asymm h), if_neg h.ne', map_zero, add_zero]
      exact CharTwo.add_self_eq_zero _
    · rw [← h, hc i i, if_neg (lt_irrefl i), if_pos rfl, add_assoc, hτ i]
      exact CharTwo.add_self_eq_zero _
    · rw [hc j i, if_neg (lt_asymm h), if_neg h.ne', hc i j, if_pos h,
        h46_sigma_herm hσ.invol (w0 j) (w0 i), add_zero]
      exact CharTwo.add_self_eq_zero _

@[expose] def hypMat (v w : Fin 3 → Fin 6 → F) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun k i =>
    if i.val % 2 = 0 then v ⟨i.val / 2, by omega⟩ k else w ⟨i.val / 2, by omega⟩ k

theorem hypGram_mul_self : hypGram F * hypGram F = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [hypGram, Fin.sum_univ_six, Matrix.one_apply]

private theorem h47_wv (hσ : ∀ c, σ (σ c) = c) {v w : Fin 3 → Fin 6 → F}
    (hvw : ∀ i j, ∑ k, σ (v i k) * w j k = if i = j then 1 else 0) (i j : Fin 3) :
    ∑ k, σ (w i k) * v j k = if i = j then 1 else 0 := by
  have key : ∑ k, σ (w i k) * v j k = σ (∑ k, σ (v j k) * w i k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hσ, mul_comm]
  rw [key, hvw j i]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]

theorem conjTr_hypMat_mul (hσ : ∀ c, σ (σ c) = c) {v w : Fin 3 → Fin 6 → F}
    (hvv : ∀ i j, ∑ k, σ (v i k) * v j k = 0)
    (hvw : ∀ i j, ∑ k, σ (v i k) * w j k = if i = j then 1 else 0)
    (hww : ∀ i j, ∑ k, σ (w i k) * w j k = 0) :
    conjTr σ (hypMat v w) * hypMat v w = hypGram F := by
  have hwv := h47_wv hσ hvw
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [hypMat, hypGram, conjTr_apply, hvv, hvw, hww, hwv]

private theorem h47_hypMat_even_col (v w : Fin 3 → Fin 6 → F) (j : Fin 3) :
    (hypMat v w).mulVec (Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F)) = v j := by
  funext k
  have h1 : (2 * j.val) / 2 = j.val := by omega
  have h2 : (2 * j.val) % 2 = 0 := by omega
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, hypMat, h1, h2]

theorem exists_unitary_of_hyp (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    {v w : Fin 3 → Fin 6 → F}
    (hvv : ∀ i j, ∑ k, σ (v i k) * v j k = 0)
    (hvw : ∀ i j, ∑ k, σ (v i k) * w j k = if i = j then 1 else 0)
    (hww : ∀ i j, ∑ k, σ (w i k) * w j k = 0) :
    ∃ g : GL (Fin 6) F, conjTr σ (g : Matrix (Fin 6) (Fin 6) F) * (g : Matrix (Fin 6) (Fin 6) F) = 1 ∧
      ∀ j : Fin 3, (g : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec j) = v j := by
  have hG2 : conjTr σ (hypMat v w) * hypMat v w = hypGram F :=
    conjTr_hypMat_mul hσ.invol hvv hvw hww
  have h2 : (hypGram F * conjTr σ (hypMat v w)) * hypMat v w = 1 := by
    rw [Matrix.mul_assoc, hG2, hypGram_mul_self]
  have h1 : hypMat v w * (hypGram F * conjTr σ (hypMat v w)) = 1 := mul_eq_one_comm.mpr h2
  refine ⟨(⟨hypMat v w, hypGram F * conjTr σ (hypMat v w), h1, h2⟩ : GL (Fin 6) F) *
    (frameGL σ ω hω)⁻¹, ?_, ?_⟩
  · have hS : frameMat σ ω * frameInv σ ω = 1 := frameMat_mul_frameInv hω
    have hG : conjTr σ (frameMat σ ω) * frameMat σ ω = hypGram F :=
      conjTr_frameMat_mul hσ.invol hω
    show conjTr σ (hypMat v w * frameInv σ ω) * (hypMat v w * frameInv σ ω) = 1
    calc conjTr σ (hypMat v w * frameInv σ ω) * (hypMat v w * frameInv σ ω)
        = conjTr σ (frameInv σ ω) * (conjTr σ (hypMat v w) * hypMat v w) * frameInv σ ω := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = conjTr σ (frameInv σ ω) * hypGram F * frameInv σ ω := by rw [hG2]
      _ = conjTr σ (frameInv σ ω) * (conjTr σ (frameMat σ ω) * frameMat σ ω) * frameInv σ ω := by
          rw [hG]
      _ = conjTr σ (frameMat σ ω * frameInv σ ω) * (frameMat σ ω * frameInv σ ω) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hS, conjTr_one, Matrix.one_mul]
  · intro j
    have hp : (frameInv σ ω).mulVec (e3uT0Vec j) =
        Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F) := by
      rw [← frameMat_mulVec_even (σ := σ) ω j, Matrix.mulVec_mulVec, frameInv_mul_frameMat hω,
        Matrix.one_mulVec]
    show (hypMat v w * frameInv σ ω).mulVec (e3uT0Vec j) = v j
    rw [← Matrix.mulVec_mulVec, hp, h47_hypMat_even_col]

theorem cmat_inv_unitary {g : GL (Fin 6) F}
    (hg : conjTr σ (g : Matrix (Fin 6) (Fin 6) F) * (g : Matrix (Fin 6) (Fin 6) F) = 1) (I J : Idx) :
    cmat g⁻¹ I J = σ (cmat g J I) := by
  have hinv : ((g⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      conjTr σ (g : Matrix (Fin 6) (Fin 6) F) := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hg
  rw [cmat_apply_det, cmat_apply_det, hinv]
  set M : Matrix (Fin 3) (Fin 3) F :=
    Matrix.of fun (i j : Fin 3) => (g : Matrix (Fin 6) (Fin 6) F) (enum J i) (enum I j) with hM
  have h1 : (Matrix.of fun (i j : Fin 3) =>
      conjTr σ (g : Matrix (Fin 6) (Fin 6) F) (enum I j) (enum J i)) = M.map σ := by
    ext i j
    simp [conjTr, hM]
  have h2 : (Matrix.of fun (i j : Fin 3) =>
      (g : Matrix (Fin 6) (Fin 6) F) (enum J j) (enum I i)) = Mᵀ := by
    ext i j
    simp [hM]
  rw [h1, h2, Matrix.det_transpose]
  exact (RingHom.map_det σ.toRingHom M).symm

theorem cmat_sigma_unitary {g : GL (Fin 6) F}
    (hg : conjTr σ (g : Matrix (Fin 6) (Fin 6) F) * (g : Matrix (Fin 6) (Fin 6) F) = 1) (I J : Idx) :
    (g : Matrix (Fin 6) (Fin 6) F).det * σ (cmat g I J) = cmat g (cmpl I) (cmpl J) := by
  obtain ⟨t, ht, hbt⟩ := bmat_eq_smul_Pm (K := F)
  set d : F := (g : Matrix (Fin 6) (Fin 6) F).det with hd
  have hd0 : d ≠ 0 := by
    have hu : IsUnit (g : Matrix (Fin 6) (Fin 6) F) := g.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  have hB := cmat_beta g
  rw [← hd, hbt, Matrix.mul_smul, Matrix.smul_mul, smul_comm d t] at hB
  have hB' : (cmat g)ᵀ * Pm * cmat g = d • Pm := smul_right_injective _ ht hB
  have h1 : cmat g * cmat g⁻¹ = 1 := by rw [← cmat_mul, mul_inv_cancel, cmat_one]
  have h2 : (d⁻¹ • (Pm * (cmat g)ᵀ * Pm)) * cmat g = 1 := by
    calc (d⁻¹ • (Pm * (cmat g)ᵀ * Pm)) * cmat g
        = d⁻¹ • (Pm * ((cmat g)ᵀ * Pm * cmat g)) := by
          rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = d⁻¹ • (Pm * (d • Pm)) := by rw [hB']
      _ = 1 := by rw [Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hd0, one_smul, Pm_mul_self]
  have h3 : cmat g⁻¹ = d⁻¹ • (Pm * (cmat g)ᵀ * Pm) := by
    calc cmat g⁻¹ = ((d⁻¹ • (Pm * (cmat g)ᵀ * Pm)) * cmat g) * cmat g⁻¹ := by
          rw [h2, Matrix.one_mul]
      _ = d⁻¹ • (Pm * (cmat g)ᵀ * Pm) := by rw [Matrix.mul_assoc _ (cmat g), h1, Matrix.mul_one]
  have h4 := congrFun (congrFun h3 J) I
  rw [cmat_inv_unitary hg J I, Matrix.smul_apply, Pm_mul_apply, Matrix.transpose_apply,
    smul_eq_mul] at h4
  rw [h4, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]

theorem theta_rho_unitary {g : GL (Fin 6) F}
    (hg : conjTr σ (g : Matrix (Fin 6) (Fin 6) F) * (g : Matrix (Fin 6) (Fin 6) F) = 1)
    (ξ : Cube F) :
    (g : Matrix (Fin 6) (Fin 6) F).det • theta σ (rho F g ξ) = rho F g (theta σ ξ) := by
  apply (cubeBasis F).ext_elem
  intro I
  show coord F ((g : Matrix (Fin 6) (Fin 6) F).det • theta σ (rho F g ξ)) I =
    coord F (rho F g (theta σ ξ)) I
  rw [coord_smul, coord_theta', coord_rho, coord_rho, map_sum, Finset.mul_sum]
  refine Fintype.sum_equiv cmplEquiv _ _ fun J => ?_
  show (g : Matrix (Fin 6) (Fin 6) F).det * σ (cmat g (cmpl I) J * coord F ξ J) =
    cmat g I (cmpl J) * coord F (theta σ ξ) (cmpl J)
  rw [coord_theta, map_mul, ← mul_assoc, cmat_sigma_unitary hg (cmpl I) J, cmpl_cmpl]

theorem det_eq_one_of_theta_fixed {g : GL (Fin 6) F}
    (hg : conjTr σ (g : Matrix (Fin 6) (Fin 6) F) * (g : Matrix (Fin 6) (Fin 6) F) = 1)
    {ξ : Cube F} (hξ0 : ξ ≠ 0) (hθ : theta σ ξ = ξ) (hρ : rho F g (pt0 F) = ξ) :
    (g : Matrix (Fin 6) (Fin 6) F).det = 1 := by
  have h := theta_rho_unitary hg (pt0 F)
  rw [hρ, theta_pt0, hρ, hθ] at h
  have h5 : (fun c : F => c • ξ) ((g : Matrix (Fin 6) (Fin 6) F).det) = (fun c : F => c • ξ) 1 := by
    simpa using h
  exact smul_left_injective F hξ0 h5

end CFSG.RankThree.GF2n.Smith81.U6Cube

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

theorem u6RootTransStatement_holds : U6RootTransStatement := by
  intro F _ _ _ f hF ξ hξ
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨hW, hne, v, hv⟩ := hξ
  subst hv
  have hθ : theta (unitaryInvolution F 2 f) (exteriorPower.ιMulti F 3 v) =
      exteriorPower.ιMulti F 3 v := mem_Wsub_iff.mp hW
  have hiso := hermF_eq_zero_of_theta_fixed_pure hσ.invol hne hθ
  obtain ⟨w, hvw, hww⟩ := exists_hyperbolic_partners hσ hne hiso
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one _)
  obtain ⟨g, hg, hgv⟩ := exists_unitary_of_hyp hσ hω hiso hvw hww
  have hρ : rho F g (pt0 F) = exteriorPower.ιMulti F 3 v := by
    rw [pt0_eq_ιMulti_T0, rho_ιMulti]
    congr 1
    funext j
    exact hgv j
  have hdet := det_eq_one_of_theta_fixed hg hne hθ hρ
  refine ⟨⟨g, CFSG.LieType.Universal.Unitary.mem_SUid.mpr ⟨hdet, hg⟩⟩, 1, one_ne_zero,
    map_one _, ?_⟩
  rw [one_smul]
  exact hρ.symm

end CFSG.RankThree.GF2n.Smith81
