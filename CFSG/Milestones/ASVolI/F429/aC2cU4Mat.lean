module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherCharTwoOrthonormal
public import CFSG.Quasithin.H13.U4ParCore
public import CFSG.Quasithin.H13.U4ParLine
public import CFSG.Quasithin.H13.U4ParOuter
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI

section Forms

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.U4Par
open LinearMap (BilinForm)

variable {F : Type} [Field F] [CharP F 2]

theorem burnsideF429a_congr_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (hsq : ∀ a : F, IsSquare a) {M : Matrix ι ι F} (hM : Mᵀ = M) (hdet : M.det ≠ 0)
    (halt : ∃ v : ι → F, v ⬝ᵥ (M *ᵥ v) ≠ 0) :
    ∃ P P' : Matrix ι ι F, P * P' = 1 ∧ Pᵀ * M * P = 1 := by
  have hBsymm : (Matrix.toBilin' M).IsSymm := ⟨fun v w => by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_mulVec, ← mulVec_transpose,
      hM, dotProduct_comm]⟩
  have hBnd : (Matrix.toBilin' M).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_of_det_ne_zero hdet)
  obtain ⟨v, hv⟩ := halt
  obtain ⟨b, hb⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_orthonormal_basis_of_charTwo hsq
      hBsymm hBnd (Or.inr ⟨v, by rw [Matrix.toBilin'_apply']; exact hv⟩)
  let e : Fin (Module.finrank F (ι → F)) ≃ ι :=
    (finCongr (Module.finrank_fintype_fun_eq_card F : Module.finrank F (ι → F) =
      Fintype.card ι)).trans (Fintype.equivFin ι).symm
  let b' := b.reindex e
  refine ⟨(Pi.basisFun F ι).toMatrix b', b'.toMatrix (Pi.basisFun F ι),
    (Pi.basisFun F ι).toMatrix_mul_toMatrix_flip b', ?_⟩
  calc ((Pi.basisFun F ι).toMatrix b')ᵀ * M * (Pi.basisFun F ι).toMatrix b'
      = ((Pi.basisFun F ι).toMatrix b')ᵀ *
          BilinForm.toMatrix (Pi.basisFun F ι) (Matrix.toBilin' M) *
          (Pi.basisFun F ι).toMatrix b' := by
        rw [BilinForm.toMatrix_basisFun, BilinForm.toMatrix'_toBilin']
    _ = BilinForm.toMatrix b' (Matrix.toBilin' M) :=
        BilinForm.toMatrix_mul_basis_toMatrix _ _ _
    _ = 1 := by
        ext i j
        rw [BilinForm.toMatrix_apply, Basis.reindex_apply, Basis.reindex_apply, hb, one_apply]
        simp only [e.symm.injective.eq_iff]

theorem burnsideF429a_congr_hyp {M : Matrix Ix Ix F} (hdet : M.det ≠ 0)
    (halt : ∀ v : Ix → F, v ⬝ᵥ (M *ᵥ v) = 0) :
    ∃ P P' : Matrix Ix Ix F, P * P' = 1 ∧ Pᵀ * M * P = hypGram 2 0 F := by
  have hBalt : (Matrix.toBilin' M).IsAlt := fun v => by
    rw [Matrix.toBilin'_apply']
    exact halt v
  have hBnd : (Matrix.toBilin' M).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_of_det_ne_zero hdet)
  obtain ⟨m, b, hd, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis _ hBalt hBnd
  have hm : m = 2 := by
    rw [Module.finrank_fintype_fun_eq_card] at hd
    simp at hd
    omega
  subst hm
  let b' := b.reindex ixEF.symm
  refine ⟨(Pi.basisFun F Ix).toMatrix b', b'.toMatrix (Pi.basisFun F Ix),
    (Pi.basisFun F Ix).toMatrix_mul_toMatrix_flip b', ?_⟩
  calc ((Pi.basisFun F Ix).toMatrix b')ᵀ * M * (Pi.basisFun F Ix).toMatrix b'
      = ((Pi.basisFun F Ix).toMatrix b')ᵀ *
          BilinForm.toMatrix (Pi.basisFun F Ix) (Matrix.toBilin' M) *
          (Pi.basisFun F Ix).toMatrix b' := by
        rw [BilinForm.toMatrix_basisFun, BilinForm.toMatrix'_toBilin']
    _ = BilinForm.toMatrix b' (Matrix.toBilin' M) :=
        BilinForm.toMatrix_mul_basis_toMatrix _ _ _
    _ = hypGram 2 0 F := by
        ext i j
        rw [BilinForm.toMatrix_apply, Basis.reindex_apply, Basis.reindex_apply, Equiv.symm_symm,
          ← BilinForm.toMatrix_apply, hb]
        rcases ix_cases i with rfl | rfl | rfl | rfl <;>
          rcases ix_cases j with rfl | rfl | rfl | rfl <;>
          simp [Matrix.J, ixEF, ie1, ie2, if1, if2, hypGram_apply, CharTwo.neg_eq]

end Forms

section Rank

open Matrix

theorem burnsideF429a_rank_single {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (i j : ι)
    {c : F} (hc : c ≠ 0) : (single i j c : Matrix ι ι F).rank = 1 := by
  apply le_antisymm
  · have e : (single i j c : Matrix ι ι F) = vecMulVec (Pi.single i c) (Pi.single j 1) := by
      ext a b
      rw [single_apply, vecMulVec_apply]
      by_cases ha : i = a <;> by_cases hb : j = b
      · subst ha; subst hb; simp
      · subst ha; simp [Pi.single_apply, Ne.symm hb, hb]
      · simp [Pi.single_apply, Ne.symm ha, ha]
      · simp [Pi.single_apply, Ne.symm ha, ha]
    rw [e]
    exact rank_vecMulVec_le _ _
  · let R : Matrix (Fin 1) ι F := Matrix.of fun _ a => if i = a then c⁻¹ else 0
    let C : Matrix ι (Fin 1) F := Matrix.of fun b _ => if j = b then 1 else 0
    have e1 : (single i j c : Matrix ι ι F) * C = Matrix.of fun a _ => if i = a then c else 0 := by
      ext a b
      rw [mul_apply]
      simp only [C, Matrix.of_apply, single_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    have e : R * single i j c * C = 1 := by
      rw [Matrix.mul_assoc, e1]
      ext a b
      rw [mul_apply]
      simp only [R, Matrix.of_apply]
      rw [Finset.sum_eq_single i]
      · fin_cases a
        fin_cases b
        simp [hc]
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    calc 1 = (1 : Matrix (Fin 1) (Fin 1) F).rank := by rw [rank_one, Fintype.card_fin]
      _ = (R * single i j c * C).rank := by rw [e]
      _ ≤ (R * single i j c).rank := rank_mul_le_left _ _
      _ ≤ (single i j c).rank := rank_mul_le_right _ _

end Rank

section Cocycle

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.HardMathSupport.Foote.ModuleExclusions

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF429a_U4_orderOf_barEquiv : orderOf (barEquiv h) = 2 := by
  apply orderOf_eq_prime
  · ext c
    rw [pow_two]
    show barEquiv h (barEquiv h c) = c
    rw [barEquiv_apply, barEquiv_apply, h.bar_bar]
  · intro h1
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    apply hc
    rw [← barEquiv_apply, h1]
    rfl

theorem burnsideF429a_U4_exists_trace_one : ∃ θ : K, θ + h.bar θ = 1 := by
  have := h.charP
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hd : c + h.bar c ≠ 0 := by
    intro h0
    apply hc
    have e : h.bar c = -c := eq_neg_of_add_eq_zero_right h0
    rw [e, CharTwo.neg_eq]
  have hdb : h.bar (c + h.bar c) = c + h.bar c := by rw [map_add, h.bar_bar, add_comm]
  refine ⟨c / (c + h.bar c), ?_⟩
  rw [map_div₀, hdb, ← add_div, div_self hd]

theorem burnsideF429a_U4_ref {θ : K} (hθ : θ + h.bar θ = 1) :
    (((1 : Matrix Ix Ix K) + single ie1 if1 θ).map h.bar)ᵀ *
        (hypGram 2 0 K + single if1 if1 1) * (1 + single ie1 if1 θ) = hypGram 2 0 K ∧
      ((1 : Matrix Ix Ix K) + single ie1 if1 θ).map h.bar =
        (1 + single ie1 if1 θ) * (1 + single ie1 if1 1) := by
  have := h.charP
  constructor
  · ext i j
    rw [mul_apply, sum_ix]
    simp only [mul_apply, sum_ix, transpose_apply, map_apply]
    rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
      simp [one_apply, single_apply, hypGram_apply] <;> grind
  · ext i j
    rw [mul_apply, sum_ix]
    simp only [map_apply]
    rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
      simp [one_apply, single_apply] <;> grind

theorem burnsideF429a_U4_cocycle_mat {G : Matrix Ix Ix K}
    (hGu : (G.map h.bar)ᵀ * hypGram 2 0 K * G = hypGram 2 0 K) (hGG : G * G.map h.bar = 1) :
    ∃ A : Matrix Ix Ix K, (A.map h.bar)ᵀ * hypGram 2 0 K * A = hypGram 2 0 K ∧
      (G * A.map h.bar = A ∨ G * A.map h.bar = A * (1 + single ie1 if1 1)) := by
  have := h.charP
  have := h.finite
  have hF2 : CharP h.fixedField 2 := charP_fixedField h
  have hsq : ∀ a : h.fixedField, IsSquare a :=
    FiniteField.isSquare_of_char_two (ringChar.eq h.fixedField 2)
  obtain ⟨B, hBdet, hB⟩ := speiser (barEquiv h) G 2 (burnsideF429a_U4_orderOf_barEquiv h) two_pos
    (by
      show G * (G * (1 : Matrix Ix Ix K).map (barEquiv h)).map (barEquiv h) = 1
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      have e : G.map (barEquiv h) = G.map h.bar := by
        ext i j
        exact barEquiv_apply h (G i j)
      rw [e]
      exact hGG)
  have eB : B.map (barEquiv h) = B.map h.bar := by
    ext i j
    exact barEquiv_apply h (B i j)
  rw [eB] at hB
  have hbb : ∀ X : Matrix Ix Ix K, (X.map h.bar).map h.bar = X := fun X => by
    ext i j
    simp [h.bar_bar]
  have hJbar : (hypGram 2 0 K).map h.bar = hypGram 2 0 K := hypGram_map _
  have hGbG : G.map h.bar * G = 1 := mul_eq_one_comm.mp hGG
  have hJG : hypGram 2 0 K * G = Gᵀ * hypGram 2 0 K := by
    calc hypGram 2 0 K * G = (Gᵀ * (G.map h.bar)ᵀ) * hypGram 2 0 K * G := by
          rw [← transpose_mul, hGbG, transpose_one, Matrix.one_mul]
      _ = Gᵀ * ((G.map h.bar)ᵀ * hypGram 2 0 K * G) := by simp only [Matrix.mul_assoc]
      _ = Gᵀ * hypGram 2 0 K := by rw [hGu]
  obtain ⟨M, hMdef⟩ : ∃ M, M = (B.map h.bar)ᵀ * hypGram 2 0 K * B := ⟨_, rfl⟩
  have hMbar' : M.map h.bar = Bᵀ * hypGram 2 0 K * B.map h.bar := by
    rw [hMdef, Matrix.map_mul, Matrix.map_mul, ← Matrix.transpose_map, hbb, hJbar]
  have hMbar : M.map h.bar = M := by
    rw [hMbar', hMdef]
    calc Bᵀ * hypGram 2 0 K * B.map h.bar
        = (G * B.map h.bar)ᵀ * hypGram 2 0 K * B.map h.bar := by rw [hB]
      _ = (B.map h.bar)ᵀ * (Gᵀ * hypGram 2 0 K) * B.map h.bar := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (B.map h.bar)ᵀ * (hypGram 2 0 K * G) * B.map h.bar := by rw [hJG]
      _ = (B.map h.bar)ᵀ * hypGram 2 0 K * (G * B.map h.bar) := by simp only [Matrix.mul_assoc]
      _ = (B.map h.bar)ᵀ * hypGram 2 0 K * B := by rw [hB]
  have hMt : Mᵀ = M := by
    have e : Mᵀ = Bᵀ * hypGram 2 0 K * B.map h.bar := by
      rw [hMdef, transpose_mul, transpose_mul, transpose_transpose, hypGram_transpose,
        Matrix.mul_assoc]
    rw [e, ← hMbar', hMbar]
  have hMdet : M.det ≠ 0 := by
    rw [hMdef, det_mul, det_mul, det_transpose]
    have h1 : (B.map h.bar).det = h.bar B.det := by rw [RingHom.map_det]; rfl
    rw [h1]
    exact mul_ne_zero (mul_ne_zero ((map_ne_zero h.bar).mpr hBdet) det_hypGram_ne_zero) hBdet
  have hMfix : ∀ i j, M i j ∈ h.fixedField := fun i j => by
    rw [h.mem_fixedField]
    have := congrFun (congrFun hMbar i) j
    simpa only [map_apply] using this
  let M₀ : Matrix Ix Ix h.fixedField := Matrix.of fun i j => ⟨M i j, hMfix i j⟩
  have hM₀ : M₀.map h.fixedField.subtype = M := by
    ext i j
    rfl
  have hM₀t : M₀ᵀ = M₀ := by
    ext i j
    have := congrFun (congrFun hMt i) j
    simpa [M₀] using this
  have hM₀det : M₀.det ≠ 0 := by
    intro h0
    apply hMdet
    rw [← hM₀, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  by_cases halt : ∀ v : Ix → h.fixedField, v ⬝ᵥ (M₀ *ᵥ v) = 0
  ·
    obtain ⟨P, -, -, hP⟩ := burnsideF429a_congr_hyp hM₀det halt
    have hPbar : (P.map h.fixedField.subtype).map h.bar = P.map h.fixedField.subtype := by
      ext i j
      exact h.mem_fixedField.mp (P i j).2
    refine ⟨B * P.map h.fixedField.subtype, ?_, Or.inl ?_⟩
    · rw [Matrix.map_mul, hPbar, transpose_mul]
      calc (P.map h.fixedField.subtype)ᵀ * (B.map h.bar)ᵀ * hypGram 2 0 K *
            (B * P.map h.fixedField.subtype)
          = (P.map h.fixedField.subtype)ᵀ * M * P.map h.fixedField.subtype := by
            rw [hMdef]; simp only [Matrix.mul_assoc]
        _ = (Pᵀ * M₀ * P).map h.fixedField.subtype := by
            rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hM₀]
        _ = hypGram 2 0 K := by rw [hP, hypGram_map]
    · rw [Matrix.map_mul, hPbar, ← Matrix.mul_assoc, hB]
  ·
    push Not at halt
    obtain ⟨θ, hθ⟩ := burnsideF429a_U4_exists_trace_one h
    obtain ⟨hR1, hR2⟩ := burnsideF429a_U4_ref h hθ
    obtain ⟨B₀, hB₀1, hB₀2⟩ : ∃ B₀ : Matrix Ix Ix K,
        (B₀.map h.bar)ᵀ * (hypGram 2 0 K + single if1 if1 1) * B₀ = hypGram 2 0 K ∧
        B₀.map h.bar = B₀ * (1 + single ie1 if1 1) := ⟨_, hR1, hR2⟩
    obtain ⟨N₀, hN₀def⟩ : ∃ N₀ : Matrix Ix Ix h.fixedField,
        N₀ = hypGram 2 0 h.fixedField + single if1 if1 1 := ⟨_, rfl⟩
    have hN₀ : N₀.map h.fixedField.subtype = hypGram 2 0 K + single if1 if1 1 := by
      rw [hN₀def, Matrix.map_add _ (map_add _), hypGram_map, Matrix.map_single, map_one]
    have hN₀t : N₀ᵀ = N₀ := by
      rw [hN₀def, transpose_add, hypGram_transpose, transpose_single]
    have hN₀det : N₀.det ≠ 0 := by
      intro h0
      have hNd : (N₀.map h.fixedField.subtype).det = 0 := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
      have h1 := congrArg Matrix.det hB₀1
      rw [det_mul, det_mul, ← hN₀, hNd, mul_zero, zero_mul] at h1
      exact det_hypGram_ne_zero h1.symm
    have hN₀alt : ∃ v : Ix → h.fixedField, v ⬝ᵥ (N₀ *ᵥ v) ≠ 0 := by
      refine ⟨Pi.single if1 1, ?_⟩
      rw [mulVec_single_one, single_dotProduct, one_mul, hN₀def]
      simp [hypGram_apply]
    obtain ⟨P₁, -, -, hP₁⟩ := burnsideF429a_congr_one hsq hM₀t hM₀det halt
    obtain ⟨P₂, P₂', hP₂P₂', hP₂⟩ := burnsideF429a_congr_one hsq hN₀t hN₀det hN₀alt
    obtain ⟨Q, hQdef⟩ : ∃ Q, Q = P₁ * P₂' := ⟨_, rfl⟩
    have hQ : Qᵀ * M₀ * Q = N₀ := by
      rw [hQdef]
      calc (P₁ * P₂')ᵀ * M₀ * (P₁ * P₂') = P₂'ᵀ * (P₁ᵀ * M₀ * P₁) * P₂' := by
            rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = P₂'ᵀ * (P₂ᵀ * N₀ * P₂) * P₂' := by rw [hP₁, hP₂]
        _ = (P₂ * P₂')ᵀ * N₀ * (P₂ * P₂') := by
            rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = N₀ := by rw [hP₂P₂', transpose_one, Matrix.one_mul, Matrix.mul_one]
    have hQbar : (Q.map h.fixedField.subtype).map h.bar = Q.map h.fixedField.subtype := by
      ext i j
      exact h.mem_fixedField.mp (Q i j).2
    refine ⟨B * Q.map h.fixedField.subtype * B₀, ?_, Or.inr ?_⟩
    · rw [Matrix.map_mul, Matrix.map_mul, hQbar, transpose_mul, transpose_mul]
      calc (B₀.map h.bar)ᵀ * ((Q.map h.fixedField.subtype)ᵀ * (B.map h.bar)ᵀ) * hypGram 2 0 K *
            (B * Q.map h.fixedField.subtype * B₀)
          = (B₀.map h.bar)ᵀ * ((Q.map h.fixedField.subtype)ᵀ * M * Q.map h.fixedField.subtype) *
              B₀ := by
            rw [hMdef]; simp only [Matrix.mul_assoc]
        _ = (B₀.map h.bar)ᵀ * ((Qᵀ * M₀ * Q).map h.fixedField.subtype) * B₀ := by
            rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hM₀]
        _ = hypGram 2 0 K := by rw [hQ, hN₀, hB₀1]
    · calc G * (B * Q.map h.fixedField.subtype * B₀).map h.bar
          = (G * B.map h.bar) * Q.map h.fixedField.subtype * B₀.map h.bar := by
            rw [Matrix.map_mul, Matrix.map_mul, hQbar]; simp only [Matrix.mul_assoc]
        _ = B * Q.map h.fixedField.subtype * (B₀ * (1 + single ie1 if1 1)) := by rw [hB, hB₀2]
        _ = B * Q.map h.fixedField.subtype * B₀ * (1 + single ie1 if1 1) := by
            simp only [Matrix.mul_assoc]

theorem burnsideF429a_U4_sadm_z0 : SAdm h 0 0 1 := by
  have := h.charP
  show (1 : K) + h.bar 1 = h.bar 0 * 0 + h.bar 0 * 0
  rw [map_one, mul_zero, add_zero]
  exact CharTwo.add_self_eq_zero 1

@[expose] noncomputable def burnsideF429a_U4_z0 : hypSU h 2 0 :=
  sElt h (burnsideF429a_U4_sadm_z0 h)

theorem burnsideF429a_U4_coe_z0 :
    (((burnsideF429a_U4_z0 h : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      1 + single ie1 if1 1 := by
  rw [burnsideF429a_U4_z0, coe_sElt]
  simp [sMat]

theorem burnsideF429a_U4_cocycle {g : hypSU h 2 0} (hg : g * frobElt h g = 1) :
    ∃ a : hypSU h 2 0, g * frobElt h a = a ∨ g * frobElt h a = a * burnsideF429a_U4_z0 h := by
  have := h.charP
  have hG := mem_hypSU.mp g.2
  have hGG : ((g : GL Ix K) : Matrix Ix Ix K) * ((g : GL Ix K) : Matrix Ix Ix K).map h.bar = 1 := by
    have e := congrArg (fun x : hypSU h 2 0 => ((x : GL Ix K) : Matrix Ix Ix K)) hg
    simpa only [coe_mul_hypSU, coe_frobElt, OneMemClass.coe_one, Units.val_one] using e
  obtain ⟨A, hAu, hA⟩ := burnsideF429a_U4_cocycle_mat h hG.1 hGG
  have hmapdet : (A.map h.bar).det = h.bar A.det := by rw [RingHom.map_det]; rfl
  have hdA : h.bar A.det * A.det = 1 := by
    have e := congrArg Matrix.det hAu
    rw [det_mul, det_mul, det_transpose, hmapdet] at e
    have hJ := det_hypGram_ne_zero (r := 2) (ε := 0) (K := K)
    have e' : (h.bar A.det * A.det - 1) * (hypGram 2 0 K).det = 0 := by linear_combination e
    exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right hJ)
  have hz0det : (1 + single ie1 if1 1 : Matrix Ix Ix K).det = 1 := by
    rw [← burnsideF429a_U4_coe_z0]
    exact (mem_hypSU.mp (burnsideF429a_U4_z0 h).2).2
  have hAbar : h.bar A.det = A.det := by
    rcases hA with hA | hA
    · have e := congrArg Matrix.det hA
      rwa [det_mul, hG.2, one_mul, hmapdet] at e
    · have e := congrArg Matrix.det hA
      rwa [det_mul, det_mul, hG.2, one_mul, hmapdet, hz0det, mul_one] at e
  have hd1 : A.det = 1 := by
    rw [hAbar] at hdA
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have e : (A.det - 1) ^ 2 = 0 := by linear_combination hdA - A.det * h2 + h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp e)
  have hAdet : A.det ≠ 0 := by rw [hd1]; exact one_ne_zero
  let a : hypSU h 2 0 :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet, mem_hypSU.mpr ⟨hAu, hd1⟩⟩
  have hcoe : ((a : GL Ix K) : Matrix Ix Ix K) = A :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero A hAdet
  refine ⟨a, ?_⟩
  rcases hA with hA | hA
  · left
    apply hypSU_ext h
    rw [coe_mul_hypSU, coe_frobElt, hcoe]
    exact hA
  · right
    apply hypSU_ext h
    rw [coe_mul_hypSU, coe_frobElt, coe_mul_hypSU, hcoe, burnsideF429a_U4_coe_z0]
    exact hA

theorem burnsideF429a_U4_z0_mul_self :
    burnsideF429a_U4_z0 h * burnsideF429a_U4_z0 h = 1 := by
  have := h.charP
  apply hypSU_ext h
  rw [coe_mul_hypSU, burnsideF429a_U4_coe_z0]
  ext i j
  rw [mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [one_apply, single_apply] <;> grind

theorem burnsideF429a_U4_frobElt_z0 : frobElt h (burnsideF429a_U4_z0 h) = burnsideF429a_U4_z0 h := by
  apply hypSU_ext h
  rw [coe_frobElt, burnsideF429a_U4_coe_z0]
  ext i j
  simp [one_apply, single_apply, apply_ite h.bar]

theorem burnsideF429a_U4_z0_ne_one : burnsideF429a_U4_z0 h ≠ 1 := by
  intro h1
  have e := congrArg (fun x : hypSU h 2 0 => ((x : GL Ix K) : Matrix Ix Ix K) ie1 if1) h1
  simp only [burnsideF429a_U4_coe_z0, OneMemClass.coe_one, Units.val_one] at e
  simp [one_apply, single_apply] at e

theorem burnsideF429a_U4_rank_z0 :
    ((((burnsideF429a_U4_z0 h : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) - 1).rank = 1 := by
  rw [burnsideF429a_U4_coe_z0, add_sub_cancel_left]
  exact burnsideF429a_rank_single _ _ one_ne_zero

theorem burnsideF429a_U4_row_of_form [CharP K 2] {X : Matrix Ix Ix K} {c : Ix}
    (hX : Xᵀ * (hypGram 2 0 K + single c c 1) * X = hypGram 2 0 K + single c c 1) (j : Ix) :
    X c j = if c = j then 1 else 0 := by
  have e := congrFun (congrFun hX j) j
  rw [mul_apply, sum_ix] at e
  simp only [mul_apply, sum_ix, transpose_apply, Matrix.add_apply, hypGram_apply,
    single_apply] at e
  have e' : X c j ^ 2 = if c = j then 1 else 0 := by
    rcases ix_cases c with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
      (first | rw [if_pos rfl] | rw [if_neg (by decide)]) <;> simp at e <;> grind
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hcj : c = j
  · rw [if_pos hcj] at e' ⊢
    have e2 : (X c j - 1) ^ 2 = 0 := by linear_combination e' - X c j * h2 + h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp e2)
  · rw [if_neg hcj] at e' ⊢
    exact pow_eq_zero_iff two_ne_zero |>.mp e'

theorem burnsideF429a_U4_z0t_mul_J :
    ((1 : Matrix Ix Ix K) + single ie1 if1 1)ᵀ * hypGram 2 0 K =
      hypGram 2 0 K + single if1 if1 1 := by
  ext a b
  rw [mul_hypGram_apply, transpose_apply]
  rcases ix_cases a with rfl | rfl | rfl | rfl <;> rcases ix_cases b with rfl | rfl | rfl | rfl <;>
    simp [one_apply, single_apply, hypGram_apply]

theorem burnsideF429a_U4_J_mul_z0t :
    hypGram 2 0 K * ((1 : Matrix Ix Ix K) + single ie1 if1 1)ᵀ =
      hypGram 2 0 K + single ie1 ie1 1 := by
  ext a b
  rw [hypGram_mul_apply, transpose_apply]
  rcases ix_cases a with rfl | rfl | rfl | rfl <;> rcases ix_cases b with rfl | rfl | rfl | rfl <;>
    simp [one_apply, single_apply, hypGram_apply]

theorem burnsideF429a_U4_comm_z0_mat [CharP K 2] {X : Matrix Ix Ix K}
    (hXu : (X.map h.bar)ᵀ * hypGram 2 0 K * X = hypGram 2 0 K)
    (hX : X * (1 + single ie1 if1 1) = (1 + single ie1 if1 1) * X.map h.bar) :
    X * (1 + single ie1 if1 1) = (1 + single ie1 if1 1) * X := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix Ix Ix K, Z = 1 + single ie1 if1 1 := ⟨_, rfl⟩
  rw [← hZ] at hX ⊢
  have hZZ : Z * Z = 1 := by
    rw [hZ]
    ext i j
    rw [mul_apply, sum_ix]
    rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
      simp [one_apply, single_apply] <;> grind
  have hZt : Zᵀ * Zᵀ = 1 := by rw [← transpose_mul, hZZ, transpose_one]
  have hXbar : X.map h.bar = Z * X * Z := by
    calc X.map h.bar = Z * Z * X.map h.bar := by rw [hZZ, Matrix.one_mul]
      _ = Z * (Z * X.map h.bar) := by rw [Matrix.mul_assoc]
      _ = Z * (X * Z) := by rw [hX]
      _ = Z * X * Z := by rw [Matrix.mul_assoc]
  have hcol : Xᵀ * (Zᵀ * hypGram 2 0 K) * X = Zᵀ * hypGram 2 0 K := by
    have e := hXu
    rw [hXbar, transpose_mul, transpose_mul] at e
    calc Xᵀ * (Zᵀ * hypGram 2 0 K) * X = (Zᵀ * Zᵀ) * (Xᵀ * (Zᵀ * hypGram 2 0 K) * X) := by
          rw [hZt, Matrix.one_mul]
      _ = Zᵀ * (Zᵀ * (Xᵀ * Zᵀ) * hypGram 2 0 K * X) := by simp only [Matrix.mul_assoc]
      _ = Zᵀ * hypGram 2 0 K := by rw [e]
  have hXu' : X * hypGram 2 0 K * (X.map h.bar)ᵀ = hypGram 2 0 K := by
    have h1 : (hypGram 2 0 K * (X.map h.bar)ᵀ * hypGram 2 0 K) * X = 1 := by
      calc (hypGram 2 0 K * (X.map h.bar)ᵀ * hypGram 2 0 K) * X =
          hypGram 2 0 K * ((X.map h.bar)ᵀ * hypGram 2 0 K * X) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hXu, hypGram_mul_self]
    have h2 := mul_eq_one_comm.mp h1
    calc X * hypGram 2 0 K * (X.map h.bar)ᵀ =
        X * (hypGram 2 0 K * (X.map h.bar)ᵀ * hypGram 2 0 K) * hypGram 2 0 K := by
          simp only [Matrix.mul_assoc, hypGram_mul_self, Matrix.mul_one]
      _ = hypGram 2 0 K := by rw [h2, Matrix.one_mul]
  have hrow : X * (hypGram 2 0 K * Zᵀ) * Xᵀ = hypGram 2 0 K * Zᵀ := by
    have e := hXu'
    rw [hXbar, transpose_mul, transpose_mul] at e
    calc X * (hypGram 2 0 K * Zᵀ) * Xᵀ = (X * (hypGram 2 0 K * Zᵀ) * Xᵀ) * (Zᵀ * Zᵀ) := by
          rw [hZt, Matrix.mul_one]
      _ = X * hypGram 2 0 K * (Zᵀ * (Xᵀ * Zᵀ)) * Zᵀ := by simp only [Matrix.mul_assoc]
      _ = hypGram 2 0 K * Zᵀ := by rw [e]
  rw [hZ, burnsideF429a_U4_z0t_mul_J] at hcol
  rw [hZ, burnsideF429a_U4_J_mul_z0t] at hrow
  have hr := burnsideF429a_U4_row_of_form hcol
  have hc : ∀ i, X i ie1 = if ie1 = i then 1 else 0 := fun i => by
    have := burnsideF429a_U4_row_of_form (X := Xᵀ) (by rwa [transpose_transpose]) i
    rwa [transpose_apply] at this
  rw [hZ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext i j
  rw [mul_apply, mul_apply, sum_ix, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [single_apply, hr, hc]

theorem burnsideF429a_U4_comm_z0 {k : hypSU h 2 0}
    (hk : k * burnsideF429a_U4_z0 h = burnsideF429a_U4_z0 h * frobElt h k) :
    k * burnsideF429a_U4_z0 h = burnsideF429a_U4_z0 h * k := by
  have := h.charP
  apply hypSU_ext h
  have e := congrArg (fun x : hypSU h 2 0 => ((x : GL Ix K) : Matrix Ix Ix K)) hk
  simp only [coe_mul_hypSU, coe_frobElt, burnsideF429a_U4_coe_z0] at e
  rw [coe_mul_hypSU, coe_mul_hypSU, burnsideF429a_U4_coe_z0]
  exact burnsideF429a_U4_comm_z0_mat h (mem_hypSU.mp k.2).1 e

end Cocycle

end CFSG.ASVolI
