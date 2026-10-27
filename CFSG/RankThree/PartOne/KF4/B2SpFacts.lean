module

public import CFSG.RankThree.PartOne.KF4.B2Surj
public import CFSG.LieType.Universal.Symplectic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.Open.StatedAPI
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Quasisimple

variable (K : Type) [Field K]

@[expose] def f4SpPerm : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![0, 2] ![3, 1]
  invFun := ![Sum.inl 0, Sum.inr 1, Sum.inl 1, Sum.inr 0]
  left_inv := by
    rintro (i | i) <;> fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem f4B2J0_submatrix :
    (f4B2J0 K).submatrix f4SpPerm f4SpPerm = fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [f4SpPerm, f4B2J0, Matrix.submatrix_apply]

@[expose] def f4SpReindex : GL (Fin 4) K ≃* GL (Fin 2 ⊕ Fin 2) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K f4SpPerm.symm).toMulEquiv

theorem coe_f4SpReindex (A : GL (Fin 4) K) :
    ((f4SpReindex K A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (A : Matrix (Fin 4) (Fin 4) K).submatrix f4SpPerm f4SpPerm := by
  ext i j
  simp [f4SpReindex, Matrix.reindex_apply]

open CFSG.ClassicalGroups.Symplectic in
theorem mem_statedSp_iff' (n : ℕ) (A : GL (Fin n ⊕ Fin n) K) :
    A ∈ CFSG.Assembly.LowTwoRank.StatedSp n K ↔
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * fromBlocks 0 1 (-1) 0 *
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = fromBlocks 0 1 (-1) 0 :=
  CFSG.Open.StatedAPI.mem_statedSp_iff

theorem mem_f4SpGroup_iff_statedSp (A : GL (Fin 4) K) :
    A ∈ f4SpGroup K ↔ f4SpReindex K A ∈ CFSG.Assembly.LowTwoRank.StatedSp 2 K := by
  rw [mem_statedSp_iff', coe_f4SpReindex, ← f4B2J0_submatrix, mem_f4SpGroup,
    Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  constructor
  · intro h
    rw [h]
  · intro h
    ext a b
    have := congrFun (congrFun h (f4SpPerm.symm a)) (f4SpPerm.symm b)
    simpa using this

@[expose] def f4SpGroup_mulEquiv_statedSp :
    f4SpGroup K ≃* CFSG.Assembly.LowTwoRank.StatedSp 2 K :=
  (MulEquiv.subgroupMap (f4SpReindex K) (f4SpGroup K)).trans
    (MulEquiv.subgroupCongr (by
      ext B
      constructor
      · rintro ⟨A, hA, rfl⟩
        exact (mem_f4SpGroup_iff_statedSp K A).1 hA
      · intro hB
        refine ⟨(f4SpReindex K).symm B, ?_, by simp⟩
        rw [SetLike.mem_coe, mem_f4SpGroup_iff_statedSp]
        simpa using hB))

theorem f4SpGroup_isQuasisimple [Finite K] (hK : 4 ≤ Nat.card K ∨ Nat.card K = 3) :
    CFSG.IsQuasisimple (f4SpGroup K) := by
  have hq : CFSG.IsQuasisimple (CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num) (by
      rcases hK with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl ⟨h, le_refl _⟩))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (f4SpGroup_mulEquiv_statedSp K).symm hq

end Quasisimple

section Commutant

variable {K L : Type} [Field K] [Field L] [Algebra K L]

local notation "E[" i ", " j "]" => (Matrix.single (i : Fin 4) (j : Fin 4) (1 : L))

omit [Algebra K L] in
theorem scalar_of_commutes_four (M : Matrix (Fin 4) (Fin 4) L)
    (h1 : M * E[1, 2] = E[1, 2] * M) (h2 : M * E[2, 1] = E[2, 1] * M)
    (h3 : M * (E[0, 1] + E[2, 3]) = (E[0, 1] + E[2, 3]) * M)
    (h4 : M * (E[1, 0] + E[3, 2]) = (E[1, 0] + E[3, 2]) * M) :
    ∃ c : L, M = c • (1 : Matrix (Fin 4) (Fin 4) L) := by
  have e1 : ∀ i j, (M * E[1, 2]) i j = (E[1, 2] * M) i j := fun i j => by rw [h1]
  have e2 : ∀ i j, (M * E[2, 1]) i j = (E[2, 1] * M) i j := fun i j => by rw [h2]
  have e3 : ∀ i j, (M * (E[0, 1] + E[2, 3])) i j = ((E[0, 1] + E[2, 3]) * M) i j :=
    fun i j => by rw [h3]
  have e4 : ∀ i j, (M * (E[1, 0] + E[3, 2])) i j = ((E[1, 0] + E[3, 2]) * M) i j :=
    fun i j => by rw [h4]
  have f01 : M 0 1 = 0 := by
    have := e1 0 2
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have f02 : M 0 2 = 0 := by
    have := e2 0 1
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have f03 : M 0 3 = 0 := by
    have := e4 0 2
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have f10 : M 1 0 = 0 := by
    have := e3 1 1
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have f12 : M 1 2 = 0 := by
    have := e2 1 1
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have g13 : M 0 2 = M 1 3 := by
    have := e3 0 3
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have f20 : M 2 0 = 0 := by
    have := e1 1 0
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination -this
  have f21 : M 2 1 = 0 := by
    have := e1 2 2
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have f23 : M 2 3 = 0 := by
    have := e1 1 3
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination -this
  have f30 : M 3 0 = 0 := by
    have := e3 3 1
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have f31 : M 3 1 = 0 := by
    have := e1 3 2
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have f32 : M 3 2 = 0 := by
    have := e2 3 1
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have d10 : M 1 1 = M 0 0 := by
    have := e4 1 0
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have d21 : M 2 2 = M 1 1 := by
    have := e2 2 1
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have d32 : M 3 3 = M 2 2 := by
    have := e4 3 2
    simp [Matrix.mul_apply, Matrix.single_apply] at this
    linear_combination this
  have f13 : M 1 3 = 0 := by rw [← g13, f02]
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, f01, f02, f03, f10, f12, f13, f20, f21, f23, f30,
      f31, f32, d10, d21, d32]


theorem scalar_of_commutes_f4SpGroup (M : Matrix (Fin 4) (Fin 4) L)
    (hM : ∀ Y ∈ f4SpGroup K, M * (Y : Matrix (Fin 4) (Fin 4) K).map (algebraMap K L) =
      (Y : Matrix (Fin 4) (Fin 4) K).map (algebraMap K L) * M) :
    ∃ c : L, M = c • (1 : Matrix (Fin 4) (Fin 4) L) := by
  have hi1 : f4Index 1 ∈ f4B2Support := (mem_f4B2Support _).2 (Or.inl rfl)
  have hi2 : f4Index 2 ∈ f4B2Support := (mem_f4B2Support _).2 (Or.inr rfl)
  have cancel : ∀ (N : Matrix (Fin 4) (Fin 4) L) (X : Matrix (Fin 4) (Fin 4) L),
      M * (1 + X) = (1 + X) * M → M * X = X * M := by
    intro N X h
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  refine scalar_of_commutes_four _ ?_ ?_ ?_ ?_
  · have h := hM _ (f4B2Equiv K ⟨xUnit Tag.F4 K (f4Index 1) 1, xUnit_mem_subsystemGroup hi1 1⟩).2
    rw [coe_f4B2Equiv, f4B2_Mat_x2] at h
    have hm : ((1 : Matrix (Fin 4) (Fin 4) K) + single (1 : Fin 4) 2 1).map (algebraMap K L) =
        1 + single (1 : Fin 4) 2 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    rw [hm] at h
    exact cancel 0 _ h
  · have h := hM _ (f4B2Equiv K ⟨yUnit Tag.F4 K (f4Index 1) 1, yUnit_mem_subsystemGroup hi1 1⟩).2
    rw [coe_f4B2Equiv, f4B2_Mat_y2] at h
    have hm : ((1 : Matrix (Fin 4) (Fin 4) K) + single (2 : Fin 4) 1 1).map (algebraMap K L) =
        1 + single (2 : Fin 4) 1 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    rw [hm] at h
    exact cancel 0 _ h
  · have h := hM _ (f4B2Equiv K ⟨xUnit Tag.F4 K (f4Index 2) 1, xUnit_mem_subsystemGroup hi2 1⟩).2
    rw [coe_f4B2Equiv, f4B2_Mat_x3] at h
    have hm : ((1 : Matrix (Fin 4) (Fin 4) K) + (single (0 : Fin 4) 1 1 + single 2 3 1)).map
        (algebraMap K L) = 1 + (single (0 : Fin 4) 1 1 + single 2 3 1) := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    rw [hm] at h
    exact cancel 0 _ h
  · have h := hM _ (f4B2Equiv K ⟨yUnit Tag.F4 K (f4Index 2) 1, yUnit_mem_subsystemGroup hi2 1⟩).2
    rw [coe_f4B2Equiv, f4B2_Mat_y3] at h
    have hm : ((1 : Matrix (Fin 4) (Fin 4) K) + (single (1 : Fin 4) 0 1 + single 3 2 1)).map
        (algebraMap K L) = 1 + (single (1 : Fin 4) 0 1 + single 3 2 1) := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    rw [hm] at h
    exact cancel 0 _ h

theorem mem_torusGroup_of_diag {q : ModGL Tag.F4 L} (hq : q ∈ subsystemGroup Tag.F4 L f4B2Support)
    (hdiag : ∀ i j, i ≠ j → (f4B2_data.Mat q) i j = 0) : q ∈ torusGroup Tag.F4 L := by
  have hSp := f4B2_Mat_mem_Sp hq
  have hD : f4B2_data.Mat q = Matrix.diagonal (fun i => f4B2_data.Mat q i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  set d : Fin 4 → L := fun i => f4B2_data.Mat q i i with hd
  have h03 : d 0 * d 3 = 1 := by
    have := congrFun (congrFun hSp 0) 3
    rw [hD] at this
    simpa [f4B2J0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, hd, mul_comm,
      mul_left_comm] using this
  have h12 : d 1 * d 2 = 1 := by
    have := congrFun (congrFun hSp 1) 2
    rw [hD] at this
    simp [f4B2J0, Matrix.mul_apply, Matrix.diagonal_apply, hd] at this
    exact this
  have hu0 : d 0 ≠ 0 := left_ne_zero_of_mul_eq_one h03
  have hu1 : d 1 ≠ 0 := left_ne_zero_of_mul_eq_one h12
  set b : Lˣ := Units.mk0 (d 0) hu0 with hb
  set a : Lˣ := Units.mk0 (d 1) hu1 * b with ha
  have hMat : f4B2_data.Mat q = f4B2_data.Mat (torus2Elt (f4Index 1) (f4Index 2) a b) := by
    rw [f4B2_Mat_torus, hD]
    congr 1
    funext i
    fin_cases i
    · simp [hb]
    · simp [ha, hb]
    · have h2 : d 2 = (d 1)⁻¹ := eq_inv_of_mul_eq_one_right h12
      simp [ha, hb, h2, mul_comm, _root_.mul_inv_rev]
    · have h3 : d 3 = (d 0)⁻¹ := eq_inv_of_mul_eq_one_right h03
      simp [hb, h3]
  have heq : (f4B2Equiv L ⟨q, hq⟩ : GL (Fin 4) L) =
      (f4B2Equiv L ⟨torus2Elt (f4Index 1) (f4Index 2) a b, torus2Elt_mem_f4B2 a b⟩ :
        GL (Fin 4) L) := by
    refine Units.ext ?_
    rw [coe_f4B2Equiv, coe_f4B2Equiv]
    exact hMat
  have hqq : q = torus2Elt (f4Index 1) (f4Index 2) a b :=
    congrArg Subtype.val ((f4B2Equiv L).injective (Subtype.ext heq))
  rw [hqq, torus2Elt]
  exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

end Commutant


end CFSG.RankThree.PartOne.KF4
