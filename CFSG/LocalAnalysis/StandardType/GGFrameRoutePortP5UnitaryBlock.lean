module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGUIso
public import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.FrameRoute.UnitaryModel

open CFSG.Assembly CFSG.SeitzReduction.UnitaryPilot CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LocalAnalysis.GLTheoremA.HSubT

variable {K : Type} [Field K] {d : ℕ}

private theorem blockComplProj_mul_eq_of_offDiag {a : Fin d → ZMod 3} {t : ZMod 3}
    {I : Finset (Fin d)} (hI : ∀ i, i ∈ I ↔ a i = t) {g : Matrix (Fin d) (Fin d) K}
    (hg : ∀ i j, a i ≠ a j → g i j = 0) :
    CFSG.SeitzReduction.LinearPilot.blockComplProj I * g =
      g * CFSG.SeitzReduction.LinearPilot.blockComplProj I := by
  ext i j
  simp only [CFSG.SeitzReduction.LinearPilot.blockComplProj, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases ha : a i = a j
  · have hmem : i ∈ I ↔ j ∈ I := by rw [hI i, hI j, ha]
    by_cases hi : i ∈ I
    · have hj : j ∈ I := hmem.mp hi
      simp [hi, hj]
    · have hj : j ∉ I := fun h => hi (hmem.mpr h)
      simp [hi, hj]
  · rw [hg i j ha, mul_zero, zero_mul]

private theorem mem_suBlock_iff (hK : Nat.card K = 4) {I : Finset (Fin d)}
    {x : LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)} :
    x ∈ suBlock hK I ↔ ∃ A : ↥(LargeEvenSUGroup (Fin d) K 2),
      A ∈ unitaryBlock (⟨Nat.prime_two, le_rfl, hK⟩ : UnitaryFieldData 2 1 K) I ∧
        LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2) A = x :=
  Iff.rfl

theorem suBlock_subgroupOf_normal (hK : Nat.card K = 4) {ζ : Kˣ} (hζ : orderOf ζ = 3)
    {a : Fin d → ZMod 3} {t : ZMod 3} {I : Finset (Fin d)} (hI : ∀ i, i ∈ I ↔ a i = t)
    (hd : d < 2 * I.card)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (a i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (a i).val))⁻¹) φ) :
    ((suBlock hK I).subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom)).Normal := by
  classical
  have hU : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, hK⟩
  refine (Subgroup.normal_subgroupOf_iff (suBlock_le_fixedSubgroup hK hζ hI hφ)).2 ?_
  intro h k hh hk
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K 2)) k
  have hg : ∀ i j, a i ≠ a j → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 :=
    (mkProj_mem_fixedSubgroup_iff hζ hI hd hφ g).mp hk
  have hblock : (unitaryBlock hU I).map (MulAut.conj g).toMonoidHom = unitaryBlock hU I :=
    map_conj_unitaryBlock_of_mul_eq hU g (blockComplProj_mul_eq_of_offDiag hI hg)
  obtain ⟨A, hA, hAeq⟩ := (mem_suBlock_iff (hK := hK)).mp hh
  have hgA : MulAut.conj g A ∈ unitaryBlock hU I := by
    have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hA
    rwa [hblock] at this
  refine (mem_suBlock_iff (hK := hK)).mpr ⟨MulAut.conj g A, hgA, ?_⟩
  rw [← hAeq]
  simp [MulAut.conj_apply, mul_assoc]

private theorem submatrix_mul_of_offDiag {I : Finset (Fin d)} {A B : Matrix (Fin d) (Fin d) K}
    (hA : ∀ i j, i ∉ I → j ∈ I → A i j = 0) :
    (Matrix.of fun i j : ↥Iᶜ => (A * B) ↑i ↑j) =
      (Matrix.of fun i j : ↥Iᶜ => A ↑i ↑j) *
        (Matrix.of fun i j : ↥Iᶜ => B ↑i ↑j) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply]
  have hzero : ∀ k ∈ (Finset.univ : Finset (Fin d)), k ∉ Iᶜ → A ↑i k * B k ↑j = 0 := by
    intro k _ hk
    have hkI : k ∈ I := by simpa using hk
    rw [hA ↑i k (Finset.mem_compl.mp i.2) hkI, zero_mul]
  rw [← Finset.sum_subset (s₁ := Iᶜ) (s₂ := Finset.univ) (Finset.subset_univ Iᶜ) hzero,
    Finset.sum_coe_sort Iᶜ (fun k : Fin d => A ↑i k * B k ↑j)]

private def blockSubmatrix (I : Finset (Fin d)) {n : ℕ} (e : ↥Iᶜ ≃ Fin n)
    (A : Matrix (Fin d) (Fin d) K) : Matrix (Fin n) (Fin n) K :=
  (Matrix.of fun i j : ↥Iᶜ => A ↑i ↑j).submatrix (⇑e.symm) (⇑e.symm)

private theorem blockSubmatrix_one {n : ℕ} (I : Finset (Fin d)) (e : ↥Iᶜ ≃ Fin n) :
    blockSubmatrix I e (1 : Matrix (Fin d) (Fin d) K) = 1 := by
  unfold blockSubmatrix
  have h : (Matrix.of fun i j : ↥Iᶜ => (1 : Matrix (Fin d) (Fin d) K) ↑i ↑j) =
      (1 : Matrix ↥Iᶜ ↥Iᶜ K) := by
    ext i j
    rw [Matrix.of_apply, Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have h2 : (↑i : Fin d) ≠ ↑j := fun hh => hij (Subtype.ext hh)
      simp [hij, h2]
  rw [h, Matrix.submatrix_one_equiv]

private theorem blockSubmatrix_mul {n : ℕ} (I : Finset (Fin d)) (e : ↥Iᶜ ≃ Fin n)
    {A B : Matrix (Fin d) (Fin d) K}
    (hA : ∀ i j, i ∉ I → j ∈ I → A i j = 0) :
    blockSubmatrix I e (A * B) = blockSubmatrix I e A * blockSubmatrix I e B := by
  unfold blockSubmatrix
  rw [submatrix_mul_of_offDiag (I := I) (A := A) (B := B) hA,
    Matrix.submatrix_mul_equiv]

private theorem entries_eq_one_of_blockSubmatrix_eq_one {n : ℕ} (I : Finset (Fin d))
    (e : ↥Iᶜ ≃ Fin n) {g : Matrix (Fin d) (Fin d) K}
    (h0 : ∀ i j, i ∈ I → j ∉ I → g i j = 0)
    (h1 : ∀ i j, i ∉ I → j ∈ I → g i j = 0)
    (hg : blockSubmatrix I e g = 1) :
    ∀ i j, (i ∉ I ∨ j ∉ I) → g i j = (1 : Matrix (Fin d) (Fin d) K) i j := by
  have hblock : ∀ i j : ↥Iᶜ, g ↑i ↑j = if i = j then (1 : K) else 0 := by
    intro i j
    have h := congrFun (congrFun hg (e i)) (e j)
    simp only [blockSubmatrix, Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_apply_apply,
      Matrix.one_apply, e.injective.eq_iff] at h
    exact h
  intro i j hij
  rcases hij with hi | hj
  · by_cases hjI : j ∈ I
    · have hne : i ≠ j := fun h => hi (h ▸ hjI)
      rw [h1 i j hi hjI, Matrix.one_apply_ne hne]
    · have hb := hblock ⟨i, by simpa using hi⟩ ⟨j, by simpa using hjI⟩
      by_cases hij' : i = j
      · subst hij'; simpa using hb
      · have h2 : (⟨i, by simpa using hi⟩ : ↥Iᶜ) ≠ ⟨j, by simpa using hjI⟩ :=
          fun hh => hij' (congrArg Subtype.val hh)
        simp [hb, hij', h2]
  · by_cases hiI : i ∈ I
    · have hne : i ≠ j := fun h => hj (h ▸ hiI)
      rw [h0 i j hiI hj, Matrix.one_apply_ne hne]
    · have hb := hblock ⟨i, by simpa using hiI⟩ ⟨j, by simpa using hj⟩
      by_cases hij' : i = j
      · subst hij'; simpa using hb
      · have h2 : (⟨i, by simpa using hiI⟩ : ↥Iᶜ) ≠ ⟨j, by simpa using hj⟩ :=
          fun hh => hij' (congrArg Subtype.val hh)
        simp [hb, hij', h2]

private theorem blockSubmatrix_unitary {n : ℕ} (I : Finset (Fin d)) {f : K → K} (hf : f 0 = 0)
    (e : ↥Iᶜ ≃ Fin n) {g : Matrix (Fin d) (Fin d) K}
    (hunit : Matrix.transpose (g.map f) * g = 1)
    (h0 : ∀ i j, i ∈ I → j ∉ I → g i j = 0) :
    Matrix.transpose ((blockSubmatrix I e g).map f) * blockSubmatrix I e g = 1 := by
  have hA : ∀ i j, i ∉ I → j ∈ I → Matrix.transpose (g.map f) i j = 0 := by
    intro i j hi hj
    rw [Matrix.transpose_apply, Matrix.map_apply, h0 j i hj hi, hf]
  have hmul := blockSubmatrix_mul I e (A := Matrix.transpose (g.map f)) (B := g) hA
  have h1eq : blockSubmatrix I e (Matrix.transpose (g.map f)) =
      Matrix.transpose ((blockSubmatrix I e g).map f) := by
    ext i j
    simp only [blockSubmatrix, Matrix.submatrix_apply, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.map_apply]
  rw [← h1eq, ← hmul, hunit, blockSubmatrix_one]

private def OffDiagZero (I : Finset (Fin d))
    (X : Subgroup ↥(LargeEvenSUGroup (Fin d) K 2)) : Prop :=
  ∀ g : ↥X,
    (∀ i j, i ∈ I → j ∉ I →
      ((((g : ↥X) : ↥(LargeEvenSUGroup (Fin d) K 2)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) i j = 0) ∧
    (∀ i j, i ∉ I → j ∈ I →
      ((((g : ↥X) : ↥(LargeEvenSUGroup (Fin d) K 2)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) i j = 0)

private theorem transpose_map_sq_mul_of_mem_largeEvenSUGroup (hU : UnitaryFieldData 2 1 K)
    {g : GL (Fin d) K} (hg : g ∈ LargeEvenSUGroup (Fin d) K 2) :
    Matrix.transpose ((g : Matrix (Fin d) (Fin d) K).map (fun x => x ^ 2)) *
      (g : Matrix (Fin d) (Fin d) K) = 1 := by
  have h := ((mem_unitarySU_iff hU).mp hg).2
  have hbar : (⇑hU.bar : K → K) = fun x => x ^ 2 := by
    funext x
    rw [UnitaryFieldData.bar_apply, show (2 : ℕ) ^ 1 = 2 from rfl]
  rw [hbar] at h
  exact h

private theorem offDiag_blocks_zero {a : Fin d → ZMod 3} {t : ZMod 3} {I : Finset (Fin d)}
    (hI : ∀ i, i ∈ I ↔ a i = t) {g : Matrix (Fin d) (Fin d) K}
    (hg : ∀ i j, a i ≠ a j → g i j = 0) :
    (∀ i j, i ∈ I → j ∉ I → g i j = 0) ∧ (∀ i j, i ∉ I → j ∈ I → g i j = 0) := by
  constructor
  · intro i j hi hj
    exact hg i j (fun h => hj ((hI j).mpr (h ▸ (hI i).mp hi)))
  · intro i j hi hj
    exact hg i j (fun h => hi ((hI i).mpr (h ▸ (hI j).mp hj)))

private theorem entries_zero_of_mem_fixed {ζ : Kˣ} (hζ : orderOf ζ = 3)
    {a : Fin d → ZMod 3} {t : ZMod 3} {I : Finset (Fin d)} (hI : ∀ i, i ∈ I ↔ a i = t)
    (hd : d < 2 * I.card)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (a i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (a i).val))⁻¹) φ)
    {g : ↥(LargeEvenSUGroup (Fin d) K 2)}
    (hg : LargeEvenProjMk _ g ∈ TauCeti.fixedSubgroup φ.toMonoidHom) :
    (∀ i j, i ∈ I → j ∉ I → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0) ∧
    (∀ i j, i ∉ I → j ∈ I → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0) :=
  offDiag_blocks_zero hI ((mkProj_mem_fixedSubgroup_iff hζ hI hd hφ g).mp hg)

private def blockHom {n : ℕ} (I : Finset (Fin d)) (e : ↥Iᶜ ≃ Fin n)
    (X : Subgroup ↥(LargeEvenSUGroup (Fin d) K 2)) (hX : OffDiagZero I X) :
    ↥X →* (Matrix (Fin n) (Fin n) K)ˣ :=
  ({ toFun := fun g => blockSubmatrix I e
      ((((g : ↥X) : ↥(LargeEvenSUGroup (Fin d) K 2)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K)
     map_one' := by simpa using blockSubmatrix_one I e
     map_mul' := fun g g' => by
       have hcoe : ((((g * g' : ↥X) : ↥(LargeEvenSUGroup (Fin d) K 2)) : GL (Fin d) K) :
           Matrix (Fin d) (Fin d) K) =
           ((((g : ↥X) : ↥(LargeEvenSUGroup (Fin d) K 2)) : GL (Fin d) K) :
             Matrix (Fin d) (Fin d) K) *
             ((((g' : ↥X) : ↥(LargeEvenSUGroup (Fin d) K 2)) : GL (Fin d) K) :
               Matrix (Fin d) (Fin d) K) := by
         simp [Subgroup.coe_mul]
       rw [hcoe]
       exact blockSubmatrix_mul I e (hX g).2 } :
      ↥X →* Matrix (Fin n) (Fin n) K).toHomUnits

private theorem blockHom_apply {n : ℕ} (I : Finset (Fin d)) (e : ↥Iᶜ ≃ Fin n)
    (X : Subgroup ↥(LargeEvenSUGroup (Fin d) K 2)) (hX : OffDiagZero I X) (g : ↥X) :
    ((blockHom I e X hX g : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) =
      blockSubmatrix I e ((((g : ↥X) : ↥(LargeEvenSUGroup (Fin d) K 2)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) :=
  MonoidHom.coe_toHomUnits _ g

private theorem blockHom_range_le_heldGU {n : ℕ} (I : Finset (Fin d)) (e : ↥Iᶜ ≃ Fin n)
    (X : Subgroup ↥(LargeEvenSUGroup (Fin d) K 2)) (hX : OffDiagZero I X)
    (hU : UnitaryFieldData 2 1 K) :
    (blockHom I e X hX).range ≤ heldGU n K (resTau hU) (resTau_invol hU) := by
  rintro x ⟨g, rfl⟩
  rw [mem_heldGU]
  have hbar : (⇑(resTau hU) : K → K) = fun x => x ^ 2 := funext (resTau_apply hU)
  rw [hbar, blockHom_apply]
  exact blockSubmatrix_unitary I (f := fun x => x ^ 2) (by simp) e
    (transpose_map_sq_mul_of_mem_largeEvenSUGroup hU
      ((g : ↥X) : ↥(LargeEvenSUGroup (Fin d) K 2)).2) (hX g).1

private theorem blockHom_ker_mem_unitaryBlock {n : ℕ} (I : Finset (Fin d))
    (e : ↥Iᶜ ≃ Fin n) (X : Subgroup ↥(LargeEvenSUGroup (Fin d) K 2))
    (hX : OffDiagZero I X) (hU : UnitaryFieldData 2 1 K) :
    ∀ g : ↥X, blockHom I e X hX g = 1 →
      ((g : ↥X) : ↥(LargeEvenSUGroup (Fin d) K 2)) ∈ unitaryBlock hU I := by
  intro g hg
  refine (mem_unitaryBlock (h := hU)).mpr ?_
  have hb : blockSubmatrix I e ((((g : ↥X) : ↥(LargeEvenSUGroup (Fin d) K 2)) :
      GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← blockHom_apply I e X hX g, hg, Units.val_one]
  exact entries_eq_one_of_blockSubmatrix_eq_one I e (hX g).1 (hX g).2 hb

private theorem exists_quotientMap (hK : Nat.card K = 4) (hU : UnitaryFieldData 2 1 K)
    {I : Finset (Fin d)} (C : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)))
    {n : ℕ} (ρ : ↥(C.comap (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))) →*
      (Matrix (Fin n) (Fin n) K)ˣ)
    (hblock : ∀ g : ↥(C.comap (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))), ρ g = 1 →
      ((g : ↥(C.comap (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2)))) :
        ↥(LargeEvenSUGroup (Fin d) K 2)) ∈ unitaryBlock hU I)
    [((suBlock hK I).subgroupOf C).Normal] :
    ∃ ψ : ↥(C.comap (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))) →*
        (↥C ⧸ (suBlock hK I).subgroupOf C),
      Function.Surjective ψ ∧ ρ.ker ≤ ψ.ker := by
  let S : Subgroup (GL (Fin d) K) := LargeEvenSUGroup (Fin d) K 2
  let ψ : ↥(C.comap (LargeEvenProjMk S)) →* (↥C ⧸ (suBlock hK I).subgroupOf C) :=
    (QuotientGroup.mk' ((suBlock hK I).subgroupOf C)).comp
      ((LargeEvenProjMk S).subgroupComap C)
  refine ⟨ψ, ?_, ?_⟩
  · exact (QuotientGroup.mk'_surjective ((suBlock hK I).subgroupOf C)).comp
      (MonoidHom.subgroupComap_surjective (LargeEvenProjMk S) C
        (QuotientGroup.mk'_surjective _))
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have hpi : (LargeEvenProjMk S) ((g : ↥(C.comap (LargeEvenProjMk S))) : ↥S) ∈
        suBlock hK I :=
      (mem_suBlock_iff (hK := hK)).mpr
        ⟨((g : ↥(C.comap (LargeEvenProjMk S))) : ↥S), hblock g hg, rfl⟩
    show QuotientGroup.mk' ((suBlock hK I).subgroupOf C)
      (⟨(LargeEvenProjMk S) ((g : ↥(C.comap (LargeEvenProjMk S))) : ↥S),
        Subgroup.mem_comap.mp g.2⟩ : ↥C) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hpi

private theorem isSolvable_range_of_le_heldGU {G : Type*} [Group G] {n : ℕ}
    (hU : UnitaryFieldData 2 1 K) {ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ} (hn : n ≤ 3)
    (hρ : ρ.range ≤ heldGU n K (resTau hU) (resTau_invol hU)) :
    Group.IsSolvable ↥ρ.range := by
  have hGU : Group.IsSolvable ↥(heldGU n K (resTau hU) (resTau_invol hU)) :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.resGU_solvable hU n hn
  exact @Group.isSolvable_of_isSolvable_injective _ _ _ _ (Subgroup.inclusion hρ)
    (Subgroup.inclusion_injective hρ) hGU

private theorem isSolvable_of_blockHom_surjective {G Q : Type*} [Group G] [Group Q] {n : ℕ}
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ) (ψ : G →* Q)
    (hρ : Group.IsSolvable ↥ρ.range) (hψ : Function.Surjective ψ) (hker : ρ.ker ≤ ψ.ker) :
    Group.IsSolvable Q := by
  have hsolvKer : Group.IsSolvable (G ⧸ ρ.ker) :=
    @Group.isSolvable_of_surjective _ _ _ _
      (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange ρ).symm.surjective hρ
  exact @Group.isSolvable_of_surjective _ _ _ _
    (QuotientGroup.lift ρ.ker ψ hker)
    (QuotientGroup.lift_surjective_of_surjective ρ.ker ψ hψ hker) hsolvKer

theorem isSolvable_fixedSubgroup_quotient_suBlock (hK : Nat.card K = 4) {ζ : Kˣ}
    (hζ : orderOf ζ = 3) {a : Fin d → ZMod 3} {t : ZMod 3} {I : Finset (Fin d)}
    (hI : ∀ i, i ∈ I ↔ a i = t) (h3 : 3 ≤ I.card) (hd : d ≤ I.card + 2)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (a i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (a i).val))⁻¹) φ)
    [((suBlock hK I).subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom)).Normal] :
    IsSolvable (↥(TauCeti.fixedSubgroup φ.toMonoidHom) ⧸
      (suBlock hK I).subgroupOf (TauCeti.fixedSubgroup φ.toMonoidHom)) := by
  classical
  have hU : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, hK⟩
  let S : Subgroup (GL (Fin d) K) := LargeEvenSUGroup (Fin d) K 2
  let C : Subgroup (LargeEvenProj S) := TauCeti.fixedSubgroup φ.toMonoidHom
  let X : Subgroup ↥S := C.comap (LargeEvenProjMk S)
  let J : Finset (Fin d) := Iᶜ
  let n : ℕ := Fintype.card ↥J
  let e : ↥J ≃ Fin n := Fintype.equivFin ↥J
  have hlt : d < 2 * I.card := by omega
  have hX : OffDiagZero I X := fun g =>
    entries_zero_of_mem_fixed hζ hI hlt hφ (Subgroup.mem_comap.mp g.2)
  let ρ : ↥X →* (Matrix (Fin n) (Fin n) K)ˣ := blockHom I e X hX
  obtain ⟨ψ, hψsurj, hkerle⟩ := exists_quotientMap hK hU (C := C) (ρ := ρ)
    (blockHom_ker_mem_unitaryBlock I e X hX hU)
  have hcardJ : n ≤ 2 := by
    have h1 : J.card = d - I.card := by simp [J, Finset.card_compl]
    have h2 : I.card ≤ d := by simpa using Finset.card_le_univ I
    have h3 : n = J.card := Fintype.card_coe J
    omega
  have hρ : Group.IsSolvable ↥ρ.range :=
    isSolvable_range_of_le_heldGU hU (by omega) (blockHom_range_le_heldGU I e X hX hU)
  exact isSolvable_of_blockHom_surjective ρ ψ hρ hψsurj hkerle

end CFSG.StandardType.FrameRoute.UnitaryModel
