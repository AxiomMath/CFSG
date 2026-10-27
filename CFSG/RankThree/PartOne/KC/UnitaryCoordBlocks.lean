module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.RankThree.PartOne.KCUnitaryCoord

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel

section Embed

variable {n : ℕ} {K : Type} [Field K]

@[expose] def coordIncl (K : Type) [Field K] (i j : Fin n) : Matrix (Fin n) (Fin 2) K :=
  Matrix.of fun k a => if k = (![i, j] a) then 1 else 0

@[expose] def coordProj (K : Type) [Field K] (i j : Fin n) : Matrix (Fin 2) (Fin n) K :=
  (coordIncl K i j)ᵀ

@[expose] def coordEmbed (K : Type) [Field K] (i j : Fin n) (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n) (Fin n) K :=
  1 + coordIncl K i j * (X - 1) * coordProj K i j

theorem sum_ite_mul_ite (u v : Fin n) :
    ∑ k : Fin n, (if k = u then (1 : K) else 0) * (if k = v then 1 else 0) =
      if u = v then 1 else 0 := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

theorem coordProj_mul_coordIncl {i j : Fin n} (hij : i ≠ j) :
    coordProj K i j * coordIncl K i j = 1 := by
  ext a b
  simp only [coordProj, coordIncl, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.one_apply, sum_ite_mul_ite]
  fin_cases a <;> fin_cases b <;> simp [hij, hij.symm]

theorem coordEmbed_mul {i j : Fin n} (hij : i ≠ j) (X Y : Matrix (Fin 2) (Fin 2) K) :
    coordEmbed K i j X * coordEmbed K i j Y = coordEmbed K i j (X * Y) := by
  have h := coordProj_mul_coordIncl (K := K) hij
  have h' : ∀ M : Matrix (Fin 2) (Fin n) K,
      coordProj K i j * (coordIncl K i j * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  unfold coordEmbed
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, h']
  abel

theorem coordEmbed_one (i j : Fin n) : coordEmbed K i j (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  simp [coordEmbed]

theorem coordEmbed_map_transpose (σ : K →+* K) (i j : Fin n) (X : Matrix (Fin 2) (Fin 2) K) :
    ((coordEmbed K i j X).map σ)ᵀ = coordEmbed K i j ((X.map σ)ᵀ) := by
  have h1 : (coordIncl K i j).map σ = coordIncl K i j := by
    ext k a
    simp only [coordIncl, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have h2 : (coordProj K i j).map σ = coordProj K i j := by
    unfold coordProj
    rw [Matrix.transpose_map, h1]
  unfold coordEmbed
  rw [Matrix.map_add _ (map_add σ), Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub σ), Matrix.map_one _ (map_zero σ) (map_one σ), h1, h2]
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_sub, Matrix.transpose_one]
  have h3 : (coordProj K i j)ᵀ = coordIncl K i j := Matrix.transpose_transpose _
  have h4 : (coordIncl K i j)ᵀ = coordProj K i j := rfl
  rw [h3, h4, Matrix.mul_assoc]

theorem diagonal_mul_coordIncl (d : Fin n → K) {i j : Fin n} (hd : d i = d j) :
    diagonal d * coordIncl K i j = d i • coordIncl K i j := by
  ext k a
  simp only [coordIncl, Matrix.diagonal_mul, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases a
  · by_cases hk : k = i <;> simp [hk]
  · by_cases hk : k = j <;> simp [hk, hd]

theorem coordProj_mul_diagonal (d : Fin n → K) {i j : Fin n} (hd : d i = d j) :
    coordProj K i j * diagonal d = d i • coordProj K i j := by
  have h := congrArg Matrix.transpose (diagonal_mul_coordIncl d hd (K := K) (i := i) (j := j))
  rw [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.diagonal_transpose] at h
  exact h

theorem diagonal_mul_coordEmbed (d : Fin n → K) {i j : Fin n} (hd : d i = d j)
    (X : Matrix (Fin 2) (Fin 2) K) :
    diagonal d * coordEmbed K i j X = coordEmbed K i j X * diagonal d := by
  unfold coordEmbed
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, diagonal_mul_coordIncl d hd, Matrix.mul_assoc _ _ (diagonal d),
    coordProj_mul_diagonal d hd]
  simp only [Matrix.smul_mul, Matrix.mul_smul]

theorem coordEmbed_diagonal (i j : Fin n) (hij : i ≠ j) (v w : K) :
    coordEmbed K i j (diagonal ![v, w]) =
      diagonal (fun k => if k = i then v else if k = j then w else 1) := by
  ext k l
  by_cases hkl : k = l
  · subst hkl
    simp only [coordEmbed, coordIncl, coordProj, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.sub_apply,
      Fin.sum_univ_two, Matrix.diagonal_apply]
    by_cases hk : k = i
    · subst hk
      simp [hij]
    · by_cases hk' : k = j
      · subst hk'
        simp [hk]
      · simp [hk, hk']
  · simp only [coordEmbed, coordIncl, coordProj, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.sub_apply,
      Fin.sum_univ_two, Matrix.diagonal_apply]
    simp [hkl]
    by_cases hk : k = i <;> by_cases hl : l = i <;> by_cases hk' : k = j <;>
      by_cases hl' : l = j <;> simp_all

theorem coordEmbed_swap_apply (i j : Fin n) (hij : i ≠ j) :
    coordEmbed K i j !![0, 1; -1, 0] i j = 1 := by
  simp [coordEmbed, coordIncl, coordProj, Matrix.mul_apply, Fin.sum_univ_two, hij, hij.symm]

@[expose] def coordEmbedHom (K : Type) [Field K] (i j : Fin n) (hij : i ≠ j) :
    Matrix (Fin 2) (Fin 2) K →* Matrix (Fin n) (Fin n) K where
  toFun := coordEmbed K i j
  map_one' := coordEmbed_one i j
  map_mul' X Y := (coordEmbed_mul hij X Y).symm

end Embed

section Group

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem coordEmbed_mem_primeFormUnitary {i j : Fin n} (hij : i ≠ j) {X : GL (Fin 2) K}
    (hX : X ∈ primeFormUnitary h (idGram K 2)) :
    Units.map (coordEmbedHom K i j hij) X ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary] at hX ⊢
  simp only [idGram, Units.val_one, Matrix.mul_one] at hX ⊢
  change ((coordEmbed K i j (X : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ *
    coordEmbed K i j (X : Matrix (Fin 2) (Fin 2) K) = 1
  rw [coordEmbed_map_transpose, coordEmbed_mul hij, hX, coordEmbed_one]

@[expose] noncomputable def coordSUHom {i j : Fin n} (hij : i ≠ j) :
    gramSU h (idGram K 2) →* primeFormUnitary h (idGram K n) :=
  ((Units.map (coordEmbedHom K i j hij)).comp (gramSU h (idGram K 2)).subtype).codRestrict _
    (fun g => coordEmbed_mem_primeFormUnitary h hij ((mem_gramSU_iff_unitary h).mp g.2).1)

@[expose] noncomputable def coordSU {i j : Fin n} (hij : i ≠ j) :
    Subgroup (primeFormUnitary h (idGram K n)) :=
  (coordSUHom h hij).range

theorem mem_coordSU_iff {i j : Fin n} (hij : i ≠ j) {A : primeFormUnitary h (idGram K n)} :
    A ∈ coordSU h hij ↔ ∃ X : GL (Fin 2) K, X ∈ gramSU h (idGram K 2) ∧
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        coordEmbed K i j (X : Matrix (Fin 2) (Fin 2) K) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩
  · rintro ⟨X, hX, hA⟩
    exact ⟨⟨X, hX⟩, Subtype.ext (Units.ext hA.symm)⟩

theorem isPerfect_gramSU_two (hq : 4 ≤ ℓ ^ f) : Group.IsPerfect (gramSU h (idGram K 2)) := by
  have hfr : Module.finrank K (Fin 2 → K) = 2 := by rw [Module.finrank_fin_fun]
  have hQ := isQuasisimple_sesqSpecialUnitaryGroup_of_two_le h (W := Fin 2 → K)
    (Hf := idForm h 2) (idForm_isSymm h 2) (idForm_separatingLeft h 2) (by omega) (by omega)
  obtain ⟨φ⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h
    (Pi.basisFun K (Fin 2)) (G := idGram K 2) (fun a b => by
      rw [Pi.basisFun_apply, Pi.basisFun_apply]
      exact gramForm_single h (idGram K 2) a b)
  exact (CFSG.LocalCores.isQuasisimple_of_mulEquiv φ hQ).1

theorem isPerfect_coordSU (hq : 4 ≤ ℓ ^ f) {i j : Fin n} (hij : i ≠ j) :
    Group.IsPerfect (coordSU h hij) := by
  have := isPerfect_gramSU_two h hq
  exact isPerfect_of_surjective (coordSUHom h hij).rangeRestrict
    (coordSUHom h hij).rangeRestrict_surjective

theorem coordSU_le_centralizer_diagonal {i j : Fin n} (hij : i ≠ j) (d : Fin n → K) (hd : d i = d j)
    {D : primeFormUnitary h (idGram K n)}
    (hD : ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal d) :
    coordSU h hij ≤ Subgroup.centralizer ({D} : Set (primeFormUnitary h (idGram K n))) := by
  intro A hA
  obtain ⟨X, -, hX⟩ := (mem_coordSU_iff h hij).mp hA
  refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (Units.ext ?_))
  change ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((D : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) = ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [hX, hD]
  exact (diagonal_mul_coordEmbed d hd _).symm

end Group

section Explicit

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def diag2 (v : Kˣ) : GL (Fin 2) K :=
  ⟨diagonal ![(v : K), ((v⁻¹ : Kˣ) : K)], diagonal ![((v⁻¹ : Kˣ) : K), (v : K)],
    by
      rw [Matrix.diagonal_mul_diagonal]
      ext a b
      fin_cases a <;> fin_cases b <;> simp,
    by
      rw [Matrix.diagonal_mul_diagonal]
      ext a b
      fin_cases a <;> fin_cases b <;> simp⟩

theorem diag2_mem (v : Kˣ) (hv : h.norm (v : K) = 1) : diag2 v ∈ gramSU h (idGram K 2) := by
  have h00 : h.bar (v : K) * (v : K) = 1 := by
    rw [mul_comm]
    exact hv
  have h11 : (h.bar (v : K))⁻¹ * (v : K)⁻¹ = 1 := by
    rw [← _root_.mul_inv_rev, mul_comm, h00, inv_one]
  refine ⟨?_, ?_⟩
  · change (((diagonal ![(v : K), ((v⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ *
      idGram K 2 * diagonal ![(v : K), ((v⁻¹ : Kˣ) : K)] = idGram K 2
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [h00, h11]
  · change Matrix.det (diagonal ![(v : K), ((v⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) = 1
    simp [Matrix.det_diagonal, Fin.prod_univ_two]

@[expose] noncomputable def swap2 : GL (Fin 2) K :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by ext a b; fin_cases a <;> fin_cases b <;> simp,
    by ext a b; fin_cases a <;> fin_cases b <;> simp⟩

theorem swap2_mem : swap2 ∈ gramSU h (idGram K 2) := by
  refine ⟨?_, ?_⟩
  · change ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * idGram K 2 *
      !![0, 1; -1, 0] = idGram K 2
    simp only [idGram, Units.val_one, Matrix.mul_one]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · change Matrix.det (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) = 1
    simp [Matrix.det_fin_two]

@[expose] noncomputable def diagonalCoord {i j : Fin n} (hij : i ≠ j) (v : Kˣ)
    (hv : h.norm (v : K) = 1) : primeFormUnitary h (idGram K n) :=
  coordSUHom h hij ⟨diag2 v, diag2_mem h v hv⟩

@[expose] noncomputable def swapCoord {i j : Fin n} (hij : i ≠ j) :
    primeFormUnitary h (idGram K n) :=
  coordSUHom h hij ⟨swap2, swap2_mem h⟩

theorem coe_diagonalCoord {i j : Fin n} (hij : i ≠ j) (v : Kˣ) (hv : h.norm (v : K) = 1) :
    ((diagonalCoord h hij v hv : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (fun k => if k = i then (v : K) else if k = j then ((v⁻¹ : Kˣ) : K) else 1) :=
  coordEmbed_diagonal i j hij (v : K) ((v⁻¹ : Kˣ) : K)

theorem swapCoord_apply {i j : Fin n} (hij : i ≠ j) :
    ((swapCoord h hij : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 1 :=
  coordEmbed_swap_apply i j hij

theorem diagonalCoord_mem_coordSU {i j : Fin n} (hij : i ≠ j) (v : Kˣ)
    (hv : h.norm (v : K) = 1) : diagonalCoord h hij v hv ∈ coordSU h hij :=
  ⟨_, rfl⟩

theorem swapCoord_mem_coordSU {i j : Fin n} (hij : i ≠ j) : swapCoord h hij ∈ coordSU h hij :=
  ⟨_, rfl⟩

end Explicit

end CFSG.RankThree.PartOne.KCUnitaryCoord
