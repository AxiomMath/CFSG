module

public import CFSG.LocalAnalysis.StandardType.GGZSNFourInputs
public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType.ZS

section Matrices

variable {K : Type} [Field K]

@[expose] def n4Mat (t : K) : Fin 4 → Matrix (Fin 4) (Fin 4) K :=
  ![pijMat 0 1 1, pijMat 1 2 1, pijMat 0 1 t, halfOnesMat 4]

@[expose] def en4Mat (t : K) : Fin 5 → Matrix (Fin 4) (Fin 4) K :=
  ![pijMat 0 1 1, pijMat 1 2 1, pijMat 0 1 t, halfOnesMat 4, diagSignMat 3]

private def gI : GaussianInt := ⟨0, 1⟩

private def gMat : Fin 5 → Matrix (Fin 4) (Fin 4) GaussianInt := ![
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
  !![0, gI, 0, 0; -gI, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, -1, -1, -1; -1, 1, -1, -1; -1, -1, 1, -1; -1, -1, -1, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]]

private def eps (i : Fin 5) : ℕ := if i = 3 then 1 else 0

private def coeff (i : Fin 5) : K := (2 : K)⁻¹ ^ eps i

private noncomputable def sqrtHom {t : K} (ht : t ^ 2 = -1) : GaussianInt →+* K :=
  Zsqrtd.lift (d := -1) ⟨t, by rw [← pow_two, ht]; norm_num⟩

private lemma sqrtHom_gI {t : K} (ht : t ^ 2 = -1) : sqrtHom ht gI = t := by
  simp [sqrtHom, gI]

private lemma inv_eq_neg_of_sq_eq_neg_one {t : K} (ht : t ^ 2 = -1) : t⁻¹ = -t := by
  have h : t * (-t) = 1 := by rw [mul_neg, ← pow_two, ht, neg_neg]
  exact (eq_inv_of_mul_eq_one_right h).symm

private lemma inv_pow_mul_pow {x : K} (hx : x ≠ 0) (m : ℕ) : x⁻¹ ^ m * x ^ m = 1 := by
  rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero m hx)]

private lemma map_smul_one {n : ℕ} (φ : GaussianInt →+* K) (a : GaussianInt) :
    ((a • 1 : Matrix (Fin n) (Fin n) GaussianInt)).map φ =
      φ a • (1 : Matrix (Fin n) (Fin n) K) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply, Matrix.smul_apply, h]

private lemma prod_map_smul {n : ℕ} (c : Fin n → K) (w : List (Fin n))
    (A : Fin n → Matrix (Fin 4) (Fin 4) K) :
    (w.map fun i => c i • A i).prod = (w.map c).prod • (w.map A).prod := by
  induction w with
  | nil => simp
  | cons i w ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      rw [smul_mul_smul_comm]

private lemma prod_map_matrix_map {n : ℕ} (φ : GaussianInt →+* K) (w : List (Fin n))
    (A : Fin n → Matrix (Fin 4) (Fin 4) GaussianInt) :
    (w.map fun i => (A i).map φ).prod = ((w.map A).prod).map φ := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih, Matrix.map_mul]

private lemma prod_map_coeff (w : List (Fin 5)) :
    (w.map (coeff (K := K))).prod = (2 : K)⁻¹ ^ (w.map eps).sum := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, coeff, ← pow_add]

private theorem prod_gMat_n4Extra :
    ((n4Extra.map Fin.castSucc).map gMat).prod = (1 : GaussianInt) • 1 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem prod_gMat_en4Extra : (en4Extra.map gMat).prod = (64 : GaussianInt) • 1 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem prod_gMat_n4ZW :
    ((n4ZW.map Fin.castSucc).map gMat).prod = (-16 : GaussianInt) • 1 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem prod_gMat_en4ZW : (en4ZW.map gMat).prod = (-16 : GaussianInt) • 1 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem pair_gMat_n4 : ∀ i j : Fin 4,
    (gMat (Fin.castSucc i) * gMat (Fin.castSucc j)) ^ nFourExp i j =
      (2 : GaussianInt) ^
        ((eps (Fin.castSucc i) + eps (Fin.castSucc j)) * nFourExp i j) • 1 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem pair_gMat_en4 : ∀ i j : Fin 5,
    (gMat i * gMat j) ^ enFourExp i j =
      (2 : GaussianInt) ^ ((eps i + eps j) * enFourExp i j) • 1 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem sum_eps_n4Extra : ((n4Extra.map Fin.castSucc).map eps).sum = 0 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem sum_eps_en4Extra : (en4Extra.map eps).sum = 6 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem sum_eps_n4ZW : ((n4ZW.map Fin.castSucc).map eps).sum = 4 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private theorem sum_eps_en4ZW : (en4ZW.map eps).sum = 4 := by
  set_option maxRecDepth 100000 in
  decide +kernel

private lemma en4Mat_eq_smul_map (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) (i : Fin 5) :
    en4Mat t i = coeff (K := K) i • (gMat i).map (sqrtHom ht) := by
  have hhalf : (1 : K) - 2⁻¹ = 2⁻¹ := by
    field_simp [h2]
    norm_num
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [en4Mat, pijMat, halfOnesMat, diagSignMat, gMat, coeff, eps, Matrix.map_apply,
      sqrtHom_gI ht, inv_eq_neg_of_sq_eq_neg_one ht, hhalf]

private lemma n4Mat_eq_smul_map (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) (i : Fin 4) :
    n4Mat t i = coeff (K := K) (Fin.castSucc i) •
      (gMat (Fin.castSucc i)).map (sqrtHom ht) := by
  have h : n4Mat t i = en4Mat t (Fin.castSucc i) := by
    fin_cases i <;> rfl
  rw [h, en4Mat_eq_smul_map h2 ht]

private lemma map_en4Mat_castSucc (t : K) (w : List (Fin 4)) :
    w.map (fun i => en4Mat t (Fin.castSucc i)) = w.map (n4Mat t) := by
  exact List.map_congr_left fun i _ => by fin_cases i <;> rfl

private lemma map_n4Mat_eq (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) (w : List (Fin 4)) :
    w.map (n4Mat t) =
      (w.map Fin.castSucc).map (fun i => coeff (K := K) i • (gMat i).map (sqrtHom ht)) := by
  rw [List.map_map]
  exact List.map_congr_left fun i _ => n4Mat_eq_smul_map h2 ht i

private lemma map_en4Mat_eq (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) (w : List (Fin 5)) :
    w.map (en4Mat t) =
      w.map (fun i => coeff (K := K) i • (gMat i).map (sqrtHom ht)) :=
  List.map_congr_left fun i _ => en4Mat_eq_smul_map h2 ht i

private lemma prod_map_coeff_gMat (φ : GaussianInt →+* K) (c : Fin 5 → K) (w : List (Fin 5))
    (a : GaussianInt) (h : (w.map gMat).prod = a • 1) :
    (w.map fun i => c i • (gMat i).map φ).prod = ((w.map c).prod * φ a) • 1 := by
  rw [prod_map_smul, prod_map_matrix_map, h, map_smul_one, smul_smul]

private lemma pair_pow_coeff_gMat (φ : GaussianInt →+* K) (c : Fin 5 → K) (i j : Fin 5)
    (e : ℕ) (a : GaussianInt) (h : (gMat i * gMat j) ^ e = a • 1) :
    ((c i • (gMat i).map φ) * (c j • (gMat j).map φ)) ^ e =
      ((c i * c j) ^ e * φ a) • 1 := by
  rw [smul_mul_smul_comm, ← Matrix.map_mul, smul_pow, ← Matrix.map_pow, h, map_smul_one,
    smul_smul]

private lemma coeff_pair_pow (h2 : (2 : K) ≠ 0) (i j : Fin 5) (e : ℕ) :
    (coeff (K := K) i * coeff (K := K) j) ^ e *
      (2 : K) ^ ((eps i + eps j) * e) = 1 := by
  rw [coeff, coeff, ← pow_add, pow_mul, ← mul_pow, inv_pow_mul_pow h2]
  simp

private lemma n4_pair_eq_one (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) (i j : Fin 4) :
    (n4Mat t i * n4Mat t j) ^ nFourExp i j = 1 := by
  rw [n4Mat_eq_smul_map h2 ht i, n4Mat_eq_smul_map h2 ht j]
  rw [pair_pow_coeff_gMat (sqrtHom ht) coeff (Fin.castSucc i)
    (Fin.castSucc j) (nFourExp i j)
    ((2 : GaussianInt) ^ ((eps (Fin.castSucc i) + eps (Fin.castSucc j)) * nFourExp i j))
    (pair_gMat_n4 i j)]
  rw [show (sqrtHom ht) ((2 : GaussianInt) ^
      ((eps (Fin.castSucc i) + eps (Fin.castSucc j)) * nFourExp i j)) =
      (2 : K) ^ ((eps (Fin.castSucc i) + eps (Fin.castSucc j)) * nFourExp i j) by
    rw [map_pow, map_ofNat]]
  rw [coeff_pair_pow h2]
  simp

private lemma en4_pair_eq_one (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) (i j : Fin 5) :
    (en4Mat t i * en4Mat t j) ^ enFourExp i j = 1 := by
  rw [en4Mat_eq_smul_map h2 ht i, en4Mat_eq_smul_map h2 ht j]
  rw [pair_pow_coeff_gMat (sqrtHom ht) coeff i j (enFourExp i j)
    ((2 : GaussianInt) ^ ((eps i + eps j) * enFourExp i j)) (pair_gMat_en4 i j)]
  rw [show (sqrtHom ht) ((2 : GaussianInt) ^ ((eps i + eps j) * enFourExp i j)) =
      (2 : K) ^ ((eps i + eps j) * enFourExp i j) by rw [map_pow, map_ofNat]]
  rw [coeff_pair_pow h2]
  simp

private lemma prod_n4Extra_n4Mat (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) :
    (n4Extra.map (n4Mat t)).prod = 1 := by
  rw [map_n4Mat_eq h2 ht, prod_map_coeff_gMat (sqrtHom ht) coeff _ 1 prod_gMat_n4Extra,
    prod_map_coeff, sum_eps_n4Extra]
  simp

private lemma prod_en4Extra_en4Mat (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) :
    (en4Extra.map (en4Mat t)).prod = 1 := by
  rw [map_en4Mat_eq h2 ht, prod_map_coeff_gMat (sqrtHom ht) coeff _ (64 : GaussianInt)
    prod_gMat_en4Extra, prod_map_coeff, sum_eps_en4Extra]
  rw [show (sqrtHom ht) (64 : GaussianInt) = (64 : K) by rw [map_ofNat],
    show (64 : K) = 2 ^ 6 by norm_num, inv_pow_mul_pow h2 6]
  simp

private lemma prod_n4ZW_n4Mat (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) :
    (n4ZW.map (n4Mat t)).prod = -1 := by
  rw [map_n4Mat_eq h2 ht, prod_map_coeff_gMat (sqrtHom ht) coeff _ (-16 : GaussianInt)
    prod_gMat_n4ZW, prod_map_coeff, sum_eps_n4ZW]
  rw [show (sqrtHom ht) (-16 : GaussianInt) = (-16 : K) by rw [map_neg, map_ofNat],
    show (-16 : K) = -(2 : K) ^ 4 by norm_num, mul_neg, inv_pow_mul_pow h2 4]
  simp

private lemma prod_en4ZW_en4Mat (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) :
    (en4ZW.map (en4Mat t)).prod = -1 := by
  rw [map_en4Mat_eq h2 ht, prod_map_coeff_gMat (sqrtHom ht) coeff _ (-16 : GaussianInt)
    prod_gMat_en4ZW, prod_map_coeff, sum_eps_en4ZW]
  rw [show (sqrtHom ht) (-16 : GaussianInt) = (-16 : K) by rw [map_neg, map_ofNat],
    show (-16 : K) = -(2 : K) ^ 4 by norm_num, mul_neg, inv_pow_mul_pow h2 4]
  simp

theorem n4Rel_n4Mat (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) : N4Rel (n4Mat t) :=
  ⟨n4_pair_eq_one h2 ht, prod_n4Extra_n4Mat h2 ht⟩

theorem en4Rel_en4Mat (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) : EN4Rel (en4Mat t) := by
  refine ⟨en4_pair_eq_one h2 ht, ?_, prod_en4Extra_en4Mat h2 ht⟩
  have hmap : (n4Extra.map Fin.castSucc).map (en4Mat t) = n4Extra.map (n4Mat t) := by
    rw [List.map_map]
    simpa [Function.comp_def] using map_en4Mat_castSucc t n4Extra
  rw [hmap]
  exact prod_n4Extra_n4Mat h2 ht

theorem prod_map_n4Mat_n4ZW (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) :
    (n4ZW.map (n4Mat t)).prod = -1 :=
  prod_n4ZW_n4Mat h2 ht

theorem prod_map_en4Mat_en4ZW (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) :
    (en4ZW.map (en4Mat t)).prod = -1 :=
  prod_en4ZW_en4Mat h2 ht

@[expose] def n4Word : List (Fin 4) := [2, 3, 0, 2, 1, 0, 2, 3, 0, 2, 1, 0, 2, 3, 0, 2, 1, 0]

private theorem prod_gMat_n4Word :
    (n4Word.map fun i => gMat (Fin.castSucc i)).prod = ((8 : GaussianInt) * gI) • 1 := by
  decide +kernel

private theorem sum_eps_n4Word : ((n4Word.map Fin.castSucc).map eps).sum = 3 := by
  decide +kernel

theorem prod_n4Mat_n4Word (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1) :
    (n4Word.map (n4Mat t)).prod = t • 1 := by
  rw [map_n4Mat_eq h2 ht,
    prod_map_coeff_gMat (sqrtHom ht) coeff
      (n4Word.map Fin.castSucc) ((8 : GaussianInt) * gI) prod_gMat_n4Word,
    prod_map_coeff, sum_eps_n4Word]
  rw [show sqrtHom ht ((8 : GaussianInt) * gI) = (8 : K) * t by
        rw [map_mul, map_ofNat, sqrtHom_gI]]
  rw [show (2 : K)⁻¹ ^ 3 * ((8 : K) * t) = t by
        rw [show (8 : K) = (2 : K) ^ 3 by norm_num, ← mul_assoc,
          inv_pow_mul_pow h2 3, one_mul]]

end Matrices

section Monoid

variable {M N : Type*} [Monoid M] [Monoid N]

theorem n4Rel_of_injective (φ : M →* N) (hφ : Function.Injective φ) {r : Fin 4 → M}
    (h : N4Rel (φ ∘ r)) : N4Rel r := by
  obtain ⟨hp, he⟩ := h
  refine ⟨fun i j => hφ ?_, hφ ?_⟩
  · simpa [map_pow, map_mul] using hp i j
  · rw [map_list_prod, List.map_map]
    simpa using he

theorem en4Rel_of_injective (φ : M →* N) (hφ : Function.Injective φ) {r : Fin 5 → M}
    (h : EN4Rel (φ ∘ r)) : EN4Rel r := by
  obtain ⟨hp, h1, h2⟩ := h
  refine ⟨fun i j => hφ ?_, hφ ?_, hφ ?_⟩
  · simpa [map_pow, map_mul] using hp i j
  · rw [map_list_prod, List.map_map]
    simpa [List.map_map] using h1
  · rw [map_list_prod, List.map_map]
    simpa using h2

end Monoid

section Transport

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U]

@[expose] noncomputable def automorphismToMatrix {n : ℕ} (f : Module.Basis (Fin n) K U) :
    (U ≃ₗ[K] U) →* Matrix (Fin n) (Fin n) K :=
  (LinearMap.toMatrixAlgEquiv f).toMonoidHom.comp
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom)

lemma automorphismToMatrix_apply {n : ℕ} (f : Module.Basis (Fin n) K U)
    (e : U ≃ₗ[K] U) :
    automorphismToMatrix f e = LinearMap.toMatrix f f (e : U →ₗ[K] U) := rfl

lemma automorphismToMatrix_injective {n : ℕ} (f : Module.Basis (Fin n) K U) :
    Function.Injective (automorphismToMatrix f) := by
  intro e₁ e₂ h
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrixAlgEquiv f).injective
  simpa [automorphismToMatrix] using h

private noncomputable def matrixToLinearEquiv {n : ℕ} (f : Module.Basis (Fin n) K U)
    (M : Matrix (Fin n) (Fin n) K) (hM : M * M = 1) : U ≃ₗ[K] U :=
  Matrix.toLinOfInv f f hM hM

private lemma toMatrix_matrixToLinearEquiv {n : ℕ} (f : Module.Basis (Fin n) K U)
    (M : Matrix (Fin n) (Fin n) K) (hM : M * M = 1) :
    automorphismToMatrix f (matrixToLinearEquiv f M hM) = M := by
  rw [automorphismToMatrix_apply]
  change LinearMap.toMatrix f f
    ((Matrix.toLinOfInv f f hM hM : U ≃ₗ[K] U) : U →ₗ[K] U) = M
  have h : ((Matrix.toLinOfInv f f hM hM : U ≃ₗ[K] U) : U →ₗ[K] U) = Matrix.toLin f f M := by
    ext x
    exact Matrix.toLinOfInv_apply f f hM hM x
  rw [h, LinearMap.toMatrix_toLin]

private lemma automorphismToMatrix_neg {n : ℕ} (f : Module.Basis (Fin n) K U) :
    automorphismToMatrix f (LinearEquiv.neg K) = -1 := by
  rw [automorphismToMatrix_apply]
  change LinearMap.toMatrix f f (-(LinearMap.id : U →ₗ[K] U)) = -1
  rw [map_neg, LinearMap.toMatrix_id]

private lemma closure_range_eq_basisClosure {n m : ℕ} (f : Module.Basis (Fin n) K U)
    (r : Fin m → Matrix (Fin n) (Fin n) K) (s : Fin m → (U ≃ₗ[K] U))
    (hs : ∀ i, automorphismToMatrix f (s i) = r i)
    (hinj : Function.Injective (automorphismToMatrix f)) :
    Subgroup.closure (Set.range s) = basisClosure f (Set.range r) := by
  rw [basisClosure]
  congr 1
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (hs i).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, hinj ((hs i).trans hi)⟩

private lemma weylN4Mats_eq_range_n4Mat (t : K) :
    weylN4Mats t = Set.range (n4Mat t) := by
  ext M
  constructor
  · intro hM
    simp only [weylN4Mats, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with h | h | h | h
    · exact ⟨0, by simp [n4Mat, h]⟩
    · exact ⟨1, by simp [n4Mat, h]⟩
    · exact ⟨2, by simp [n4Mat, h]⟩
    · exact ⟨3, by simp [n4Mat, h]⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [n4Mat, weylN4Mats]

private lemma weylEN4Mats_eq_range_en4Mat (t : K) :
    weylEN4Mats t = Set.range (en4Mat t) := by
  ext M
  constructor
  · intro hM
    simp only [weylEN4Mats, Set.mem_insert_iff, weylN4Mats, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hM
    rcases hM with h | h | h | h | h
    · exact ⟨4, by simp [en4Mat, h]⟩
    · exact ⟨0, by simp [en4Mat, h]⟩
    · exact ⟨1, by simp [en4Mat, h]⟩
    · exact ⟨2, by simp [en4Mat, h]⟩
    · exact ⟨3, by simp [en4Mat, h]⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [en4Mat, weylEN4Mats, weylN4Mats]

theorem exists_n4_tuple (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1)
    (f : Module.Basis (Fin 4) K U) :
    ∃ s : Fin 4 → (U ≃ₗ[K] U), (∀ i, LinearMap.toMatrix f f (s i : U →ₗ[K] U) = n4Mat t i) ∧
      Subgroup.closure (Set.range s) = basisClosure f (weylN4Mats t) ∧ N4Rel s ∧
      (n4ZW.map s).prod = LinearEquiv.neg K := by
  classical
  have hrel := n4Rel_n4Mat h2 ht
  have hsq : ∀ i : Fin 4, n4Mat t i * n4Mat t i = 1 := by
    intro i
    have h := hrel.1 i i
    have hii : nFourExp i i = 1 := by fin_cases i <;> rfl
    simpa [hii] using h
  let s : Fin 4 → (U ≃ₗ[K] U) := fun i => matrixToLinearEquiv f (n4Mat t i) (hsq i)
  have hs : ∀ i, automorphismToMatrix f (s i) = n4Mat t i :=
    fun i => toMatrix_matrixToLinearEquiv f (n4Mat t i) (hsq i)
  have hcomp : automorphismToMatrix f ∘ s = n4Mat t := funext hs
  refine ⟨s, fun i => hs i, ?_, ?_, ?_⟩
  · rw [weylN4Mats_eq_range_n4Mat]
    exact closure_range_eq_basisClosure f (n4Mat t) s hs (automorphismToMatrix_injective f)
  · apply n4Rel_of_injective (automorphismToMatrix f) (automorphismToMatrix_injective f)
    simpa [hcomp] using hrel
  · apply automorphismToMatrix_injective f
    rw [map_list_prod, List.map_map, hcomp, prod_map_n4Mat_n4ZW h2 ht,
      automorphismToMatrix_neg]

theorem exists_en4_tuple (h2 : (2 : K) ≠ 0) {t : K} (ht : t ^ 2 = -1)
    (f : Module.Basis (Fin 4) K U) :
    ∃ s : Fin 5 → (U ≃ₗ[K] U), (∀ i, LinearMap.toMatrix f f (s i : U →ₗ[K] U) = en4Mat t i) ∧
      Subgroup.closure (Set.range s) = basisClosure f (weylEN4Mats t) ∧ EN4Rel s ∧
      (en4ZW.map s).prod = LinearEquiv.neg K := by
  classical
  have hrel := en4Rel_en4Mat h2 ht
  have hsq : ∀ i : Fin 5, en4Mat t i * en4Mat t i = 1 := by
    intro i
    have h := hrel.1 i i
    have hii : enFourExp i i = 1 := by fin_cases i <;> rfl
    simpa [hii] using h
  let s : Fin 5 → (U ≃ₗ[K] U) := fun i => matrixToLinearEquiv f (en4Mat t i) (hsq i)
  have hs : ∀ i, automorphismToMatrix f (s i) = en4Mat t i :=
    fun i => toMatrix_matrixToLinearEquiv f (en4Mat t i) (hsq i)
  have hcomp : automorphismToMatrix f ∘ s = en4Mat t := funext hs
  refine ⟨s, fun i => hs i, ?_, ?_, ?_⟩
  · rw [weylEN4Mats_eq_range_en4Mat]
    exact closure_range_eq_basisClosure f (en4Mat t) s hs (automorphismToMatrix_injective f)
  · apply en4Rel_of_injective (automorphismToMatrix f) (automorphismToMatrix_injective f)
    simpa [hcomp] using hrel
  · apply automorphismToMatrix_injective f
    rw [map_list_prod, List.map_map, hcomp, prod_map_en4Mat_en4ZW h2 ht,
      automorphismToMatrix_neg]

end Transport

end CFSG.StandardType.ZS

end
