module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphAlgebra

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition
open CFSG.LocalAnalysis.ComponentInitial

private theorem psuA4k_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ psuAlg B, ∀ b ∈ psuAlg B, a * b = b * a := by
  have hgen : ∀ a ∈ psuAlg B, a * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * a := by
    intro a ha
    refine Algebra.adjoin_induction
      (p := fun x _ => x * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * x) ?_ ?_ ?_ ?_ ha
    · rintro x ⟨s, hs, rfl⟩
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rfl
    · intro r
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
    · intro x y hx hy hpx hpy
      rw [add_mul, mul_add, hpx, hpy]
    · intro x y hx hy hpx hpy
      rw [Matrix.mul_assoc x y (B : Matrix (Fin n) (Fin n) K), hpy,
        ← Matrix.mul_assoc x (B : Matrix (Fin n) (Fin n) K) y, hpx,
        Matrix.mul_assoc (B : Matrix (Fin n) (Fin n) K) x y]
  intro a ha b hb
  refine Algebra.adjoin_induction (p := fun x _ => a * x = x * a) ?_ ?_ ?_ ?_ hb
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hgen a ha
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  · intro x y hx hy hpx hpy
    rw [mul_add, add_mul, hpx, hpy]
  · intro x y hx hy hpx hpy
    rw [← Matrix.mul_assoc a x y, hpx, Matrix.mul_assoc x a y, hpy,
      ← Matrix.mul_assoc x y a]

private theorem psuA4k_psi_iff_theta_dag {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (a : Matrix (Fin n) (Fin n) K) :
    psuPsi h X a = a ↔ psuTheta h X a = psuDag h a := by
  constructor
  · intro hh
    have h1 : psuTheta h X (psuDag h a) = a := by
      rwa [psuPsi] at hh
    have h2 := congrArg (psuTheta h X) h1
    rw [psuTheta_theta h X S.X_sq (psuDag h a)] at h2
    exact h2.symm
  · intro hh
    rw [psuPsi, ← hh, psuTheta_theta h X S.X_sq a]

private theorem psuA4k_kind_congr {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (X B : GL (Fin n) K)
    {e e' : Matrix (Fin n) (Fin n) K}
    (hD : (psuDag h e = e) ↔ (psuDag h e' = e'))
    (hPsi : (psuPsi h X e = e) ↔ (psuPsi h X e' = e'))
    (hT : psuPsiTrivial h X B e ↔ psuPsiTrivial h X B e')
    (hE : (psuPsi h X e = psuDag h e) ↔ (psuPsi h X e' = psuDag h e')) :
    psuKind h X B e' = psuKind h X B e := by
  classical
  unfold psuKind
  by_cases hD1 : psuDag h e = e
  · have hD2 : psuDag h e' = e' := hD.mp hD1
    by_cases hP1 : psuPsi h X e = e
    · have hP2 : psuPsi h X e' = e' := hPsi.mp hP1
      simp [hD1, hD2, hP1, hP2]
    · have hP2 : ¬ (psuPsi h X e' = e') := fun hx => hP1 (hPsi.mpr hx)
      simp [hD1, hD2, hP1, hP2]
  · have hD2 : ¬ (psuDag h e' = e') := fun hx => hD1 (hD.mpr hx)
    by_cases hP1 : psuPsi h X e = e
    · have hP2 : psuPsi h X e' = e' := hPsi.mp hP1
      by_cases hT1 : psuPsiTrivial h X B e
      · have hT2 : psuPsiTrivial h X B e' := hT.mp hT1
        simp [hD1, hD2, hP1, hP2, hT1, hT2]
      · have hT2 : ¬ psuPsiTrivial h X B e' := fun hx => hT1 (hT.mpr hx)
        simp [hD1, hD2, hP1, hP2, hT1, hT2]
    · have hP2 : ¬ (psuPsi h X e' = e') := fun hx => hP1 (hPsi.mpr hx)
      by_cases hE1 : psuPsi h X e = psuDag h e
      · have hE2 : psuPsi h X e' = psuDag h e' := hE.mp hE1
        simp [hD1, hD2, hP1, hP2, hE1, hE2]
      · have hE2 : ¬ (psuPsi h X e' = psuDag h e') := fun hx => hE1 (hE.mpr hx)
        simp [hD1, hD2, hP1, hP2, hE1, hE2]

private theorem psuA4k_T_iff {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) :
    psuPsiTrivial h X B e ↔
      ∀ a ∈ psuAlg B, psuTheta h X (a * e) = psuDag h (a * e) := by
  simp only [psuPsiTrivial]
  constructor
  · intro hh a ha
    exact (psuA4k_psi_iff_theta_dag S (a * e)).mp (hh a ha)
  · intro hh a ha
    exact (psuA4k_psi_iff_theta_dag S (a * e)).mpr (hh a ha)

private theorem psuA4k_D_dag {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (e : Matrix (Fin n) (Fin n) K) :
    (psuDag h (psuDag h e) = psuDag h e) ↔ (psuDag h e = e) := by
  rw [psuDag_dag h e]
  exact eq_comm

private theorem psuA4k_Psi_dag {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) :
    (psuPsi h X (psuDag h e) = psuDag h e) ↔ (psuPsi h X e = e) := by
  rw [psuA4k_psi_iff_theta_dag S (psuDag h e), psuA4k_psi_iff_theta_dag S e,
    psuTheta_dag h X S.X_mem S.X_sq e, psuDag_dag h e]
  constructor
  · intro hh
    have hh' := congrArg (psuDag h) hh
    simpa only [psuDag_dag] using hh'
  · intro hh
    rw [hh, psuDag_dag]

private theorem psuA4k_T_dag {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ psuAlg B) :
    psuPsiTrivial h X B (psuDag h e) ↔ psuPsiTrivial h X B e := by
  have hdag : psuDag h e ∈ psuAlg B := (psuGraph_star_mem S e he).1
  rw [psuA4k_T_iff S (psuDag h e), psuA4k_T_iff S e]
  constructor
  · intro hh a ha
    have hb : psuDag h a ∈ psuAlg B := (psuGraph_star_mem S a ha).1
    have h0 := hh (psuDag h a) hb
    rw [← psuDag_mul, psuA4k_comm B e he a ha] at h0
    rw [psuTheta_dag h X S.X_mem S.X_sq (a * e)] at h0
    have h1 := congrArg (psuDag h) h0
    simpa only [psuDag_dag] using h1
  · intro hh a ha
    have hb : psuDag h a ∈ psuAlg B := (psuGraph_star_mem S a ha).1
    have h0 := hh (psuDag h a) hb
    have h1 : a * psuDag h e = psuDag h (psuDag h a * e) := by
      rw [psuDag_mul, psuDag_dag]
      exact psuA4k_comm B a ha (psuDag h e) hdag
    rw [h1, psuTheta_dag h X S.X_mem S.X_sq (psuDag h a * e), h0]

private theorem psuA4k_E_dag {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) :
    (psuPsi h X (psuDag h e) = psuDag h (psuDag h e)) ↔
      (psuPsi h X e = psuDag h e) := by
  simp only [psuPsi, psuDag_dag h e, psuTheta_dag h X S.X_mem S.X_sq e]
  exact ⟨fun hh => by rw [hh], fun hh => by
    have hh' := congrArg (psuDag h) hh
    simpa only [psuDag_dag] using hh'⟩

private theorem psuA4_kind_dag {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ psuAlg B) :
    psuKind h X B (psuDag h e) = psuKind h X B e := by
  exact psuA4k_kind_congr h X B (psuA4k_D_dag h e).symm (psuA4k_Psi_dag S e).symm
    (psuA4k_T_dag S he).symm (psuA4k_E_dag S e).symm

private theorem psuA4k_dag_psi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) :
    psuDag h (psuPsi h X e) = psuTheta h X e := by
  rw [psuPsi, ← psuTheta_dag h X S.X_mem S.X_sq (psuDag h e), psuDag_dag h e]

private theorem psuA4k_D_psi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) :
    (psuDag h (psuPsi h X e) = psuPsi h X e) ↔ (psuDag h e = e) := by
  rw [psuA4k_dag_psi S e]
  change (psuTheta h X e = psuTheta h X (psuDag h e)) ↔ (psuDag h e = e)
  constructor
  · intro hh
    have hh' := congrArg (psuTheta h X) hh
    rw [psuTheta_theta h X S.X_sq e, psuTheta_theta h X S.X_sq (psuDag h e)] at hh'
    exact hh'.symm
  · intro hh
    rw [hh]

private theorem psuA4k_Psi_psi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) :
    (psuPsi h X (psuPsi h X e) = psuPsi h X e) ↔ (psuPsi h X e = e) := by
  rw [psuPsi_psi h X S.X_mem S.X_sq e]
  exact eq_comm

private theorem psuA4k_Tpsi_pt {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ psuAlg B)
    {a : Matrix (Fin n) (Fin n) K} (ha : a ∈ psuAlg B) :
    (psuPsi h X (a * psuPsi h X e) = a * psuPsi h X e) ↔
      (psuPsi h X (psuPsi h X a * e) = psuPsi h X a * e) := by
  simp only [psuPsi_mul, psuPsi_psi h X S.X_mem S.X_sq e, psuPsi_psi h X S.X_mem S.X_sq a]
  rw [psuA4k_comm B e he (psuPsi h X a) (psuGraph_star_mem S a ha).2,
    psuA4k_comm B a ha (psuPsi h X e) (psuGraph_star_mem S e he).2]
  exact eq_comm

private theorem psuA4k_T_psi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ psuAlg B) :
    psuPsiTrivial h X B (psuPsi h X e) ↔ psuPsiTrivial h X B e := by
  constructor
  · intro hh b hb
    unfold psuPsiTrivial at hh
    have ha : psuPsi h X b ∈ psuAlg B := (psuGraph_star_mem S b hb).2
    have h0 := hh (psuPsi h X b) ha
    rw [psuA4k_Tpsi_pt S he ha, psuPsi_psi h X S.X_mem S.X_sq b] at h0
    exact h0
  · intro hh a ha
    unfold psuPsiTrivial at hh
    have ha' : psuPsi h X a ∈ psuAlg B := (psuGraph_star_mem S a ha).2
    have h0 := hh (psuPsi h X a) ha'
    rw [← psuA4k_Tpsi_pt S he ha] at h0
    exact h0

private theorem psuA4k_E_psi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (e : Matrix (Fin n) (Fin n) K) :
    (psuPsi h X (psuPsi h X e) = psuDag h (psuPsi h X e)) ↔
      (psuPsi h X e = psuDag h e) := by
  rw [psuPsi_psi h X S.X_mem S.X_sq e, psuA4k_dag_psi S e]
  change (e = psuTheta h X e) ↔ (psuTheta h X (psuDag h e) = psuDag h e)
  constructor
  · intro hh
    have hh' := congrArg (psuDag h) hh
    rw [← psuTheta_dag h X S.X_mem S.X_sq e] at hh'
    exact hh'.symm
  · intro hh
    have hh' := congrArg (psuDag h) hh
    rw [← psuTheta_dag h X S.X_mem S.X_sq (psuDag h e), psuDag_dag h e] at hh'
    exact hh'.symm

private theorem psuA4_kind_psi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ psuAlg B) :
    psuKind h X B (psuPsi h X e) = psuKind h X B e := by
  exact psuA4k_kind_congr h X B (psuA4k_D_psi S e).symm (psuA4k_Psi_psi S e).symm
    (psuA4k_T_psi S he).symm (psuA4k_E_psi S e).symm

private lemma psuA4r_rank_fromBlocks (F : Type) [Field F] (r s : ℕ) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)).rank = r := by
  classical
  have h : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin r => (1 : F)) (fun _ : Fin s => (0 : F))) := by
    rw [← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, Matrix.diagonal_zero]
  rw [h, Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

private lemma psuA4r_rank_map {F E : Type} [Field F] [Field E] (φ : F →+* E) {m : Type}
    [Fintype m] [DecidableEq m] (M : Matrix m m F) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVf : IsUnit (V.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hV.map φ.mapMatrix)
  have hUf : IsUnit (U.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hU.map φ.mapMatrix)
  have hE : (M.map φ).rank = ((V.map φ) * (M.map φ) * (U.map φ)).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUf,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVf]
  have h1 : (V * M * U).map φ =
      ((Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) F) 0 0
        (0 : Matrix (Fin (Fintype.card m - M.rank)) (Fin (Fintype.card m - M.rank)) F)).submatrix
          e e).map φ := by rw [h]
  simp only [Matrix.map_mul, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_zero _ (map_zero φ)] at h1
  rw [hE, h1, Matrix.rank_submatrix, psuA4r_rank_fromBlocks]

private lemma psuA4r_rank_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) (M : Matrix ι ι F) :
    Matrix.rank (formAdj σ G M) = Matrix.rank M := by
  have hX : (G⁻¹ * Matrix.transpose (M.map σ)).rank = M.rank := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹ (Matrix.transpose (M.map σ))
      (Matrix.isUnit_nonsing_inv_det G hG), Matrix.rank_transpose, psuA4r_rank_map σ M]
  unfold formAdj
  rw [Matrix.rank_mul_eq_left_of_isUnit_det G (G⁻¹ * Matrix.transpose (M.map σ)) hG, hX]

private theorem psuA4_rank_dag {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (e : Matrix (Fin n) (Fin n) K) : Matrix.rank (psuDag h e) = Matrix.rank e := by
  have hJ : IsUnit (psuJ n K) := (AutPSU.gramJ n).isUnit
  have hG : IsUnit (psuJ n K).det := (Matrix.isUnit_iff_isUnit_det (psuJ n K)).mp hJ
  simpa [psuDag] using psuA4r_rank_formAdj h.bar hG e

private theorem psuA4_rank_psi {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) :
    Matrix.rank (psuPsi h X e) = Matrix.rank e := by
  have hXdet : IsUnit ((X : Matrix (Fin n) (Fin n) K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp X.isUnit
  have hXinvdet : IsUnit (((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (X⁻¹).isUnit
  have hexp : psuPsi h X e = (X : Matrix (Fin n) (Fin n) K) * (psuDag h e).map h.bar *
      ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  rw [hexp, Matrix.mul_assoc,
    Matrix.rank_mul_eq_right_of_isUnit_det (X : Matrix (Fin n) (Fin n) K)
      ((psuDag h e).map h.bar * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hXdet,
    Matrix.rank_mul_eq_left_of_isUnit_det
      ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ((psuDag h e).map h.bar) hXinvdet,
    psuA4r_rank_map h.bar (psuDag h e), psuA4_rank_dag h e]

private lemma psuA4r_card_eq_of_map {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (e e' : Matrix ι ι F) (he : e ∈ A) (he' : e' ∈ A)
    (φ : Matrix ι ι F → Matrix ι ι F)
    (hφA : ∀ a ∈ A, φ a ∈ A)
    (hφφ : ∀ a ∈ A, φ (φ a) = a)
    (hφe : ∀ a ∈ A, φ (a * e) = φ a * e')
    (hφe' : ∀ a ∈ A, φ (a * e') = φ a * e) :
    Nat.card {x // x ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)} =
      Nat.card {x // x ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e')} := by
  classical
  let Me : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  let Me' : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e')
  have hMe : ∀ x : Matrix ι ι F, x ∈ Me ↔ ∃ a ∈ A, a * e = x := by
    intro x
    change x ∈ Submodule.map (LinearMap.mulRight F e) (Subalgebra.toSubmodule A) ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, h⟩
      refine ⟨a, ?_, ?_⟩
      · simpa using ha
      · rw [LinearMap.mulRight_apply] at h
        exact h
    · rintro ⟨a, ha, h⟩
      exact ⟨a, by simpa using ha, by rw [LinearMap.mulRight_apply]; exact h⟩
  have hMe' : ∀ x : Matrix ι ι F, x ∈ Me' ↔ ∃ a ∈ A, a * e' = x := by
    intro x
    change x ∈ Submodule.map (LinearMap.mulRight F e') (Subalgebra.toSubmodule A) ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, h⟩
      refine ⟨a, ?_, ?_⟩
      · simpa using ha
      · rw [LinearMap.mulRight_apply] at h
        exact h
    · rintro ⟨a, ha, h⟩
      exact ⟨a, by simpa using ha, by rw [LinearMap.mulRight_apply]; exact h⟩
  have hsube : ∀ x ∈ Me, x ∈ A := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (hMe x).mp hx
    exact A.mul_mem ha he
  have hsube' : ∀ x ∈ Me', x ∈ A := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (hMe' x).mp hx
    exact A.mul_mem ha he'
  let f : Me → Me' := fun x =>
    let a := Classical.choose ((hMe x.1).mp x.2)
    let ha : a ∈ A := (Classical.choose_spec ((hMe x.1).mp x.2)).1
    let hae : a * e = x.1 := (Classical.choose_spec ((hMe x.1).mp x.2)).2
    ⟨φ x.1, (hMe' (φ x.1)).mpr
      ⟨φ a, hφA a ha, (hφe a ha).symm.trans (congrArg φ hae)⟩⟩
  let g : Me' → Me := fun y =>
    let a := Classical.choose ((hMe' y.1).mp y.2)
    let ha : a ∈ A := (Classical.choose_spec ((hMe' y.1).mp y.2)).1
    let hae : a * e' = y.1 := (Classical.choose_spec ((hMe' y.1).mp y.2)).2
    ⟨φ y.1, (hMe (φ y.1)).mpr
      ⟨φ a, hφA a ha, (hφe' a ha).symm.trans (congrArg φ hae)⟩⟩
  have hleft : ∀ x : Me, g (f x) = x := by
    intro x
    apply Subtype.ext
    change φ (φ x.1) = x.1
    exact hφφ x.1 (hsube x.1 x.2)
  have hright : ∀ y : Me', f (g y) = y := by
    intro y
    apply Subtype.ext
    change φ (φ y.1) = y.1
    exact hφφ y.1 (hsube' y.1 y.2)
  have hcard : Nat.card Me = Nat.card Me' :=
    Nat.card_congr { toFun := f, invFun := g, left_inv := hleft, right_inv := hright }
  exact hcard

private lemma psuA4r_card_to_finrank {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] (A : Subalgebra F (Matrix ι ι F)) (e e' : Matrix ι ι F)
    (h : Nat.card {x // x ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)} =
      Nat.card {x // x ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e')}) :
    blockDegree A e = blockDegree A e' := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let Me : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  let Me' : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e')
  have h' : Fintype.card Me = Fintype.card Me' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact h
  have h1 : Fintype.card F ^ Module.finrank F Me =
      Fintype.card F ^ Module.finrank F Me' := by
    rw [← Module.card_eq_pow_finrank, ← Module.card_eq_pow_finrank, h']
  have hF : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hfin : Module.finrank F Me = Module.finrank F Me' :=
    Nat.pow_right_injective hF h1
  exact hfin

private theorem psuA4_deg_dag {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ psuAlg B) :
    blockDegree (psuAlg B) (psuDag h e) = blockDegree (psuAlg B) e := by
  have hde : psuDag h e ∈ psuAlg B := (psuGraph_star_mem S e he).1
  have hcard := psuA4r_card_eq_of_map (psuAlg B) e (psuDag h e) he hde (psuDag h)
    (fun a ha => (psuGraph_star_mem S a ha).1)
    (fun a ha => psuDag_dag h a)
    (fun a ha => by
      rw [psuDag_mul]
      exact psuA4k_comm B (psuDag h e) (psuGraph_star_mem S e he).1 (psuDag h a)
        (psuGraph_star_mem S a ha).1)
    (fun a ha => by
      rw [psuDag_mul, psuDag_dag]
      exact psuA4k_comm B e he (psuDag h a) (psuGraph_star_mem S a ha).1)
  exact (psuA4r_card_to_finrank (psuAlg B) e (psuDag h e) hcard).symm

private theorem psuA4_deg_psi {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ psuAlg B) :
    blockDegree (psuAlg B) (psuPsi h X e) = blockDegree (psuAlg B) e := by
  have hpe : psuPsi h X e ∈ psuAlg B := (psuGraph_star_mem S e he).2
  have hcard := psuA4r_card_eq_of_map (psuAlg B) e (psuPsi h X e) he hpe (psuPsi h X)
    (fun a ha => (psuGraph_star_mem S a ha).2)
    (fun a ha => psuPsi_psi h X S.X_mem S.X_sq a)
    (fun a ha => by
      rw [psuPsi_mul]
      exact psuA4k_comm B (psuPsi h X e) (psuGraph_star_mem S e he).2 (psuPsi h X a)
        (psuGraph_star_mem S a ha).2)
    (fun a ha => by
      rw [psuPsi_mul, psuPsi_psi h X S.X_mem S.X_sq e]
      exact psuA4k_comm B e he (psuPsi h X a) (psuGraph_star_mem S a ha).2)
  exact (psuA4r_card_to_finrank (psuAlg B) e (psuPsi h X e) hcard).symm

theorem psuGraph_orbit_invariant {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {h : UnitaryFieldData 2 f K} {X B : GL (Fin n) K} (S : PSUGraphSetting h n X B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (psuAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    (psuKind h X B (psuDag h e) = psuKind h X B e ∧ Matrix.rank (psuDag h e) = Matrix.rank e ∧
        blockDegree (psuAlg B) (psuDag h e) = blockDegree (psuAlg B) e) ∧
      (psuKind h X B (psuPsi h X e) = psuKind h X B e ∧
        Matrix.rank (psuPsi h X e) = Matrix.rank e ∧
        blockDegree (psuAlg B) (psuPsi h X e) = blockDegree (psuAlg B) e) := by
  have heA : e ∈ psuAlg B := ((hP.1 e).1 he).1
  exact ⟨⟨psuA4_kind_dag S heA, psuA4_rank_dag h e, psuA4_deg_dag S heA⟩,
    ⟨psuA4_kind_psi S heA, psuA4_rank_psi h X e, psuA4_deg_psi S heA⟩⟩

end CFSG.StandardType
