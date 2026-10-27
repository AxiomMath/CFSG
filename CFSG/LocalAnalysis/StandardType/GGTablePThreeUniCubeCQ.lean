module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeBridge
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotWeakCTNormal
import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestSURank
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniTorusDiag
import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitPlane
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryDiag
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryFamily
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAKit
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotWeakCTSeitz

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

section Helpers

open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.UnitaryPilot
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

private noncomputable def psuEquivPSUg {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n) :
    (↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) ⧸
        (unitaryScalars h n : Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)))) ≃*
      (↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) ⧸
        ((LargeEvenScalars (Fin n) K).subgroupOf
          (LargeEvenSUGroup (Fin n) K (2 ^ f)))) := by
  haveI hM : (unitaryScalars h n :
      Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))).Normal :=
    normOneScalars_normal h (LargeEvenSUGroup (Fin n) K (2 ^ f)) n
  haveI hN : ((LargeEvenScalars (Fin n) K).subgroupOf
      (LargeEvenSUGroup (Fin n) K (2 ^ f))).Normal :=
    Subgroup.normal_subgroupOf (N := LargeEvenScalars (Fin n) K)
  have hsub : (unitaryScalars h n :
      Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))) =
      (LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K (2 ^ f)) := by
    rw [unitaryScalars_eq h hn]
    rfl
  exact @QuotientGroup.quotientMulEquivOfEq _ _
    (unitaryScalars h n : Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)))
    ((LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K (2 ^ f)))
    hM hN hsub

private lemma psuEquivPSUg_mk {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n)
    (A : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))) :
    psuEquivPSUg h hn (QuotientGroup.mk A :
        ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) ⧸
          (unitaryScalars h n : Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)))) =
      (QuotientGroup.mk A : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) ⧸
        ((LargeEvenScalars (Fin n) K).subgroupOf
          (LargeEvenSUGroup (Fin n) K (2 ^ f)))) := by
  haveI hM : (unitaryScalars h n :
      Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))).Normal :=
    normOneScalars_normal h (LargeEvenSUGroup (Fin n) K (2 ^ f)) n
  haveI hN : ((LargeEvenScalars (Fin n) K).subgroupOf
      (LargeEvenSUGroup (Fin n) K (2 ^ f))).Normal :=
    Subgroup.normal_subgroupOf (N := LargeEvenScalars (Fin n) K)
  simp only [psuEquivPSUg]
  exact @QuotientGroup.quotientMulEquivOfEq_mk _ _
    (unitaryScalars h n : Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)))
    ((LargeEvenScalars (Fin n) K).subgroupOf (LargeEvenSUGroup (Fin n) K (2 ^ f)))
    hM hN _ A

private lemma psuEquivPSUg_unitaryProj {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n)
    (A : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))) :
    psuEquivPSUg h hn (unitaryProj h n A) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) A := by
  haveI hM : (unitaryScalars h n :
      Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))).Normal :=
    normOneScalars_normal h (LargeEvenSUGroup (Fin n) K (2 ^ f)) n
  haveI hN : ((LargeEvenScalars (Fin n) K).subgroupOf
      (LargeEvenSUGroup (Fin n) K (2 ^ f))).Normal :=
    Subgroup.normal_subgroupOf (N := LargeEvenScalars (Fin n) K)
  haveI hMU : (unitaryScalars h n : Subgroup ↥(unitarySU 2 f K n)).Normal := inferInstance
  exact psuEquivPSUg_mk h hn A

private lemma psuEquivPSUg_symm_largeEvenProjMk {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)
    (hn : 1 ≤ n) (g : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))) :
    (psuEquivPSUg h hn).symm
        (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) g) = unitaryProj h n g := by
  haveI hM : (unitaryScalars h n :
      Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))).Normal :=
    normOneScalars_normal h (LargeEvenSUGroup (Fin n) K (2 ^ f)) n
  haveI hN : ((LargeEvenScalars (Fin n) K).subgroupOf
      (LargeEvenSUGroup (Fin n) K (2 ^ f))).Normal :=
    Subgroup.normal_subgroupOf (N := LargeEvenScalars (Fin n) K)
  haveI hMU : (unitaryScalars h n : Subgroup ↥(unitarySU 2 f K n)).Normal := inferInstance
  rw [← psuEquivPSUg_unitaryProj h hn g, MulEquiv.symm_apply_apply]

private noncomputable def psuEquivPSUgZero {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K) :
    unitaryPSU h 0 ≃* PSUg 0 K (2 ^ f) := by
  haveI : Subsingleton ↥(unitarySU 2 f K 0) :=
    ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i _ => Fin.elim0 i))⟩
  haveI : Subsingleton ↥(LargeEvenSUGroup (Fin 0) K (2 ^ f)) :=
    ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i _ => Fin.elim0 i))⟩
  exact
    { toFun := fun _ => 1
      invFun := fun _ => 1
      left_inv := fun x => Subsingleton.elim _ _
      right_inv := fun x => Subsingleton.elim _ _
      map_mul' := fun x y => Subsingleton.elim _ _ }

private lemma mem_unitaryBlock_LE {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)
    {I : Finset (Fin n)} {g : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))} :
    g ∈ (unitaryBlock h I : Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))) ↔
      ∀ i j, (i ∉ I ∨ j ∉ I) → ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        (1 : Matrix (Fin n) (Fin n) K) i j := by
  constructor
  · intro hg
    exact (mem_unitaryBlock (h := h) (A := (show ↥(unitarySU 2 f K n) from g))).mp hg
  · intro hg
    exact (mem_unitaryBlock (h := h) (A := (show ↥(unitarySU 2 f K n) from g))).mpr hg

private lemma mem_eigenspace_diagonal {K : Type} [Field K] {n : ℕ} {w : Fin n → K} {μ : K} {v : Fin n → K} :
    v ∈ Module.End.eigenspace (Matrix.toLin' (Matrix.diagonal w)) μ ↔
      ∀ i, w i ≠ μ → v i = 0 := by
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  constructor
  · intro h i hi
    have h' := congrFun h i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h'
    have h'' : (w i - μ) * v i = 0 := by rw [sub_mul, h', sub_self]
    exact (mul_eq_zero.mp h'').resolve_left (sub_ne_zero.mpr hi)
  · intro h
    funext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hi : w i = μ
    · rw [hi]
    · rw [h i hi, mul_zero, mul_zero]

private lemma single_apply_eq_one {K : Type} [Field K] {n : ℕ} (i j : Fin n) :
    (Pi.single j (1 : K) : Fin n → K) i = (1 : Matrix (Fin n) (Fin n) K) i j := by
  by_cases h : i = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Matrix.one_apply_ne h]

private lemma mulVec_conj {K : Type} [Field K] {n : ℕ} (S D : GL (Fin n) K) (v : Fin n → K) :
    (((S * D * S⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ
        ((S : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (S : Matrix (Fin n) (Fin n) K) *ᵥ ((D : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
  have hSin : (((S⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [show (((S * D * S⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      (S : Matrix (Fin n) (Fin n) K) * (D : Matrix (Fin n) (Fin n) K) *
        ((S⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) by
    rw [Units.val_mul, Units.val_mul]]
  simp only [Matrix.mulVec_mulVec, Matrix.one_mulVec, mul_assoc, hSin, one_mul, mul_one]

private lemma mulVec_injective {K : Type} [Field K] {n : ℕ} (S : GL (Fin n) K) :
    Function.Injective (fun v : Fin n → K => (S : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
  have hSin : (((S⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  intro a b hab
  have h := congrArg (fun v : Fin n → K =>
    (((S⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ v) hab
  simp only [Matrix.mulVec_mulVec, Matrix.one_mulVec, hSin, one_mul, mul_one] at h
  exact h

private lemma mem_cubeEigen_conj {K : Type} [Field K] {n : ℕ} (S D : GL (Fin n) K) {v : Fin n → K} {μ : K} :
    ((S : Matrix (Fin n) (Fin n) K) *ᵥ v) ∈ cubeEigen (S * D * S⁻¹) μ ↔
      v ∈ cubeEigen D μ := by
  show ((S : Matrix (Fin n) (Fin n) K) *ᵥ v) ∈
      Module.End.eigenspace (Matrix.toLin' (((S * D * S⁻¹ : GL (Fin n) K)) :
        Matrix (Fin n) (Fin n) K)) μ ↔
      v ∈ Module.End.eigenspace (Matrix.toLin' ((D : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) μ
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff,
    Matrix.toLin'_apply, Matrix.toLin'_apply]
  constructor
  · intro h
    have h' : (S : Matrix (Fin n) (Fin n) K) *ᵥ ((D : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        (S : Matrix (Fin n) (Fin n) K) *ᵥ (μ • v) := by
      rw [← mulVec_conj S D v, h, Matrix.mulVec_smul]
    exact mulVec_injective S h'
  · intro h
    rw [mulVec_conj S D v, h, Matrix.mulVec_smul]

private lemma finrank_cubeEigen_conj {K : Type} [Field K] {n : ℕ} {S D d : GL (Fin n) K}
    (hs : S * D * S⁻¹ = d) (μ : K) :
    Module.finrank K (cubeEigen d μ) = Module.finrank K (cubeEigen D μ) := by
  subst hs
  have hSin : (S : Matrix (Fin n) (Fin n) K) *
      (((S⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let e : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofBijective (Matrix.toLin' (S : Matrix (Fin n) (Fin n) K))
      ⟨by
        intro a b hab
        exact mulVec_injective S (by simpa [Matrix.toLin'_apply] using hab),
       by
        intro y
        refine ⟨(((S⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ y, ?_⟩
        rw [Matrix.toLin'_apply]
        rw [Matrix.mulVec_mulVec, hSin, Matrix.one_mulVec]⟩
  have hmap : cubeEigen (S * D * S⁻¹) μ =
      Submodule.map (Matrix.toLin' (S : Matrix (Fin n) (Fin n) K)) (cubeEigen D μ) := by
    refine Submodule.ext fun y => ?_
    rw [Submodule.mem_map]
    constructor
    · intro hy
      refine ⟨(((S⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ y, ?_, ?_⟩
      · refine (mem_cubeEigen_conj S D
            (v := (((S⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ y)
            (μ := μ)).mp ?_
        rw [Matrix.mulVec_mulVec, hSin, Matrix.one_mulVec]
        exact hy
      · rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hSin, Matrix.one_mulVec]
    · rintro ⟨x, hx, rfl⟩
      rw [Matrix.toLin'_apply]
      exact (mem_cubeEigen_conj S D (v := x) (μ := μ)).mpr hx
  rw [hmap]
  have heq : (e : (Fin n → K) →ₗ[K] (Fin n → K)) =
      Matrix.toLin' (S : Matrix (Fin n) (Fin n) K) := by
    ext x; rfl
  rw [← heq]
  exact LinearEquiv.finrank_map_eq e (cubeEigen D μ)

private lemma mem_cubeEigen_diag {K : Type} [Field K] {n : ℕ} {τ : Fin n → Kˣ} {ν : K} {v : Fin n → K} :
    v ∈ cubeEigen (SectionRank.OddCover.diagHom n τ) ν ↔
      ∀ i, (τ i : K) ≠ ν → v i = 0 := by
  show v ∈ Module.End.eigenspace (Matrix.toLin' (((SectionRank.OddCover.diagHom n τ :
    GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) ν ↔ _
  rw [SectionRank.OddCover.coe_diagHom]
  exact mem_eigenspace_diagonal

private lemma single_mem_cubeEigen_diag {K : Type} [Field K] {n : ℕ} (τ : Fin n → Kˣ) (i : Fin n) :
    (Pi.single i 1 : Fin n → K) ∈
      cubeEigen (SectionRank.OddCover.diagHom n τ) (τ i) := by
  rw [mem_cubeEigen_diag]
  intro j hj
  have hji : j ≠ i := fun h => hj (by rw [h])
  rw [Pi.single_eq_of_ne hji]

private lemma gramForm_one_single {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K) (i : Fin n)
    (y : Fin n → K) :
    gramForm h (1 : Matrix (Fin n) (Fin n) K) (Pi.single i 1) y = y i := by
  rw [gramForm_apply, Matrix.one_mulVec, dotProduct, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, map_one, one_mul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, map_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma eigSub_diag_eq_unitaryBlock {K : Type} [Field K] {f n : ℕ} [DecidableEq K]
    (h : UnitaryFieldData 2 f K) (τ : Fin n → Kˣ) (hτ : ∀ i, (τ i : K) ^ 3 = 1) (μ : K) :
    eigSub (2 ^ f) (SectionRank.OddCover.diagHom n τ) μ =
      (unitaryBlock h (Finset.univ.filter (fun i => (τ i : K) = μ)) :
        Subgroup ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))) := by
  classical
  set I := Finset.univ.filter (fun i => (τ i : K) = μ) with hI
  apply le_antisymm
  · intro g hg
    refine (mem_unitaryBlock_LE h (g := g)).mpr ?_
    have hcol : ∀ j, j ∉ I → ∀ i, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        (1 : Matrix (Fin n) (Fin n) K) i j := by
      intro j hj i
      have hj' : (τ j : K) ≠ μ := by
        simpa only [hI, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hfix : (g : GL (Fin n) K) *ᵥ (Pi.single j 1 : Fin n → K) =
          (Pi.single j 1 : Fin n → K) :=
        hg (τ j) (hτ j) hj' _ (single_mem_cubeEigen_diag τ j)
      have h := congrFun hfix i
      rw [Matrix.mulVec_single_one] at h
      simpa only [Matrix.col_apply, single_apply_eq_one] using h
    intro i j hij
    rcases hij with hi | hj
    · by_cases hjI : j ∉ I
      · exact hcol j hjI i
      · have hi' : (τ i : K) ≠ μ := by
          simpa only [hI, Finset.mem_filter, Finset.mem_univ, true_and] using hi
        have hij' : i ≠ j := by
          intro h'
          apply hi
          rw [h']
          simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
          by_contra hji
          exact hjI (by
            simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hji)
        have hSU : (g : GL (Fin n) K) ∈ gramSU h (1 : Matrix (Fin n) (Fin n) K) := by
          rw [← unitarySU_eq_gramSU h n]; exact g.2
        have hiso := ((mem_gramSU_iff_isometry).mp hSU).1
        have hfix : (g : GL (Fin n) K) *ᵥ (Pi.single i 1 : Fin n → K) =
            (Pi.single i 1 : Fin n → K) :=
          hg (τ i) (hτ i) hi' _ (single_mem_cubeEigen_diag τ i)
        have h1 := hiso (Pi.single i 1) (Pi.single j 1)
        rw [hfix, gramForm_one_single, gramForm_one_single,
          Pi.single_eq_of_ne hij'] at h1
        rw [Matrix.mulVec_single_one, Matrix.col_apply] at h1
        rw [h1, Matrix.one_apply_ne hij']
    · exact hcol j hj i
  · intro g hg
    have hg' : ∀ i j, (i ∉ I ∨ j ∉ I) →
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
          (1 : Matrix (Fin n) (Fin n) K) i j :=
      (mem_unitaryBlock_LE h (g := g)).mp hg
    intro ν hν hνμ v hv
    rw [mem_cubeEigen_diag] at hv
    funext i
    rw [Matrix.mulVec_apply, dotProduct]
    rw [Finset.sum_eq_single i]
    · by_cases hvi : v i = 0
      · rw [hvi, mul_zero]
      · have hiν : (τ i : K) = ν := by
          by_contra hcon; exact hvi (hv i hcon)
        have hiI : i ∉ I := by
          simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hiν]; exact hνμ
        rw [Matrix.row_apply, hg' i i (Or.inl hiI), Matrix.one_apply_eq, one_mul]
    · intro b _ hb
      by_cases hvb : v b = 0
      · rw [hvb, mul_zero]
      · have hbν : (τ b : K) = ν := by
          by_contra hcon; exact hvb (hv b hcon)
        have hbI : b ∉ I := by
          simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hbν]; exact hνμ
        rw [Matrix.row_apply, hg' i b (Or.inr hbI), Matrix.one_apply_ne (Ne.symm hb), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma finrank_cubeEigen_diag {K : Type} [Field K] {n : ℕ} [DecidableEq K] (τ : Fin n → Kˣ) (μ : K) :
    Module.finrank K (cubeEigen (SectionRank.OddCover.diagHom n τ) μ) =
      (Finset.univ.filter (fun i => (τ i : K) = μ)).card := by
  show Module.finrank K (Module.End.eigenspace (Matrix.toLin'
    (((SectionRank.OddCover.diagHom n τ : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K)) μ) = _
  rw [SectionRank.OddCover.coe_diagHom]
  rw [CFSG.LocalAnalysis.GLTheoremA.CanonU3.finrank_eigenspace_diagonal
    (fun i => (τ i : K)) μ]
  congr 1
  exact Finset.filter_congr_decidable _ _ _

private lemma eigBlock_diag_eq_blockSU {K : Type} [Field K] {f n : ℕ} [DecidableEq K]
    (h : UnitaryFieldData 2 f K) (τ : Fin n → Kˣ) (hτ : ∀ i, (τ i : K) ^ 3 = 1)
    (hn : 1 ≤ n) (μ : K) :
    (eigBlock (2 ^ f) (SectionRank.OddCover.diagHom n τ) μ).map
        ((psuEquivPSUg h hn).symm).toMonoidHom =
      blockSU h (Finset.univ.filter (fun i => (τ i : K) = μ)) := by
  have hsub := eigSub_diag_eq_unitaryBlock h τ hτ μ
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [eigBlock, Subgroup.mem_map] at hy
    obtain ⟨g, hg, hgy⟩ := hy
    rw [← hgy] at hyx
    have hyx' : (psuEquivPSUg h hn).symm
        (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) g) = x := hyx
    rw [psuEquivPSUg_symm_largeEvenProjMk h hn g] at hyx'
    rw [mem_blockSU]
    exact ⟨(show ↥(unitarySU 2 f K n) from g), hsub ▸ hg, hyx'⟩
  · intro hx
    rw [mem_blockSU] at hx
    obtain ⟨A, hA, hAx⟩ := hx
    refine Subgroup.mem_map.mpr ⟨LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))
      (show ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) from A), ?_, ?_⟩
    · rw [eigBlock, Subgroup.mem_map]
      exact ⟨(show ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) from A), hsub.symm ▸ hA, rfl⟩
    · change (psuEquivPSUg h hn).symm
        (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))
          (show ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) from A)) = x
      rw [psuEquivPSUg_symm_largeEvenProjMk h hn (show ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) from A)]
      exact hAx

private noncomputable def quotientCenterMulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
  QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e (Subgroup.map_center_eq e)

private noncomputable def quotientCenterMapEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (K : Subgroup G) :
    (K.map e.toMonoidHom) ⧸ Subgroup.center (K.map e.toMonoidHom) ≃* K ⧸ Subgroup.center K :=
  quotientCenterMulEquiv (e.subgroupMap K).symm

private noncomputable def topQuotientCenterEquiv (G : Type*) [Group G]
    (hcenter : Subgroup.center G = ⊥) :
    (⊤ : Subgroup G) ⧸ Subgroup.center (⊤ : Subgroup G) ≃* G :=
  (QuotientGroup.congr (Subgroup.center (⊤ : Subgroup G)) (Subgroup.center G)
      Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)).trans
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot)

private theorem diag_centerQuot {K : Type} [Field K] {f n : ℕ} [DecidableEq K]
    (h : UnitaryFieldData 2 f K) (τ : Fin n → Kˣ)
    (hτ : ∀ i, (τ i : K) ^ 3 = 1) (hn : 4 ≤ n) (μ : K) :
    Nonempty (eigBlock (2 ^ f) (SectionRank.OddCover.diagHom n τ) μ ⧸
        Subgroup.center (eigBlock (2 ^ f) (SectionRank.OddCover.diagHom n τ) μ) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (Module.finrank K
        (cubeEigen (SectionRank.OddCover.diagHom n τ) μ))) K (2 ^ f))) := by
  classical
  set I := Finset.univ.filter (fun i => (τ i : K) = μ) with hI
  have hn1 : 1 ≤ n := by omega
  have hfin := finrank_cubeEigen_diag τ μ
  rw [← hI] at hfin
  have hblock := eigBlock_diag_eq_blockSU h τ hτ hn1 μ
  rw [← hI] at hblock
  have eq1 : eigBlock (2 ^ f) (SectionRank.OddCover.diagHom n τ) μ ⧸
      Subgroup.center (eigBlock (2 ^ f) (SectionRank.OddCover.diagHom n τ) μ) ≃*
      blockSU h I ⧸ Subgroup.center (blockSU h I) := by
    rw [← hblock]
    exact (quotientCenterMapEquiv ((psuEquivPSUg h hn1).symm)
      (eigBlock (2 ^ f) (SectionRank.OddCover.diagHom n τ) μ)).symm
  by_cases hcard : I.card < n
  · by_cases h0 : I.card = 0
    · refine ⟨?_⟩
      rw [hfin]
      exact eq1.trans ((blockSUQuotientCenterEquiv h hcard).trans (h0.symm ▸ psuEquivPSUgZero h))
    · have hI1 : 1 ≤ I.card := by omega
      refine ⟨?_⟩
      rw [hfin]
      exact eq1.trans ((blockSUQuotientCenterEquiv h hcard).trans (psuEquivPSUg h hI1))
  · have hIuniv : I = Finset.univ := by
      apply Finset.eq_univ_of_card
      have hle : I.card ≤ n := by
        have h1 : I.card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ I)
        rwa [Finset.card_univ, Fintype.card_fin] at h1
      have hcardn : I.card = n := by omega
      simpa [Fintype.card_fin] using hcardn
    have hcenter : Subgroup.center (unitaryPSU h n) = ⊥ :=
      center_unitaryPSU_eq_bot h (by omega) (by
        intro h
        have h1 : n = 3 := congrArg Prod.fst h
        omega)
    have eq2 : blockSU h I ⧸ Subgroup.center (blockSU h I) ≃* unitaryPSU h n := by
      rw [hIuniv, blockSU_univ]
      exact topQuotientCenterEquiv (unitaryPSU h n) hcenter
    refine ⟨?_⟩
    rw [hfin, hIuniv, Finset.card_univ, Fintype.card_fin]
    exact (eq1.trans eq2).trans (psuEquivPSUg h hn1)

private lemma conj_mulVec_eq {K : Type} [Field K] {n : ℕ} (S g : Matrix (Fin n) (Fin n) K) (v w : Fin n → K)
    (hw : w = S *ᵥ v) (hS : S⁻¹ * S = 1) (hg : g *ᵥ w = w) :
    (S⁻¹ * g * S) *ᵥ v = v := by
  subst hw
  rw [mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg]
  rw [Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]

private lemma conj_mulVec_eq_inv {K : Type} [Field K] {n : ℕ} (S x : Matrix (Fin n) (Fin n) K) (w : Fin n → K)
    (hS : S * S⁻¹ = 1) (hx : x *ᵥ (S⁻¹ *ᵥ w) = S⁻¹ *ᵥ w) :
    (S * x * S⁻¹) *ᵥ w = w := by
  rw [mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx]
  rw [Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]

private lemma eigSub_conj {K : Type} [Field K] {f n : ℕ} (S : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)))
    (D d : GL (Fin n) K) (hs : (S : GL (Fin n) K) * D * (S : GL (Fin n) K)⁻¹ = d) (μ : K) :
    eigSub (2 ^ f) d μ = (eigSub (2 ^ f) D μ).map (MulAut.conj S).toMonoidHom := by
  subst hs
  ext g
  constructor
  · intro hg
    refine Subgroup.mem_map.mpr ⟨S⁻¹ * g * S, ?_, ?_⟩
    · intro ν hν hνμ v hv
      have hv' : (S : GL (Fin n) K) *ᵥ v ∈
          cubeEigen ((S : GL (Fin n) K) * D * (S : GL (Fin n) K)⁻¹) ν :=
        (mem_cubeEigen_conj (S : GL (Fin n) K) D (v := v) (μ := ν)).mpr hv
      have hg' := hg ν hν hνμ ((S : GL (Fin n) K) *ᵥ v) hv'
      have hSS : ((((S : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) *
          ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
        simpa using congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K))
          (inv_mul_cancel (S : GL (Fin n) K))
      have hcoe : (((S⁻¹ * g * S : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))) :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (((S : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) *
          (((g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
          ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        simp [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcoe]
      exact conj_mulVec_eq ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        (((g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) v
        ((S : GL (Fin n) K) *ᵥ v) rfl hSS hg'
    · change S * (S⁻¹ * g * S) * S⁻¹ = g
      group
  · rintro ⟨x, hx, rfl⟩
    intro ν hν hνμ w hw
    have hSS : (((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((S : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K)) = 1 := by
      simpa using congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K))
        (mul_inv_cancel (S : GL (Fin n) K))
    have hv : (((S : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈
        cubeEigen D ν := by
      refine (mem_cubeEigen_conj (S : GL (Fin n) K) D
        (v := (((S : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) *ᵥ w) (μ := ν)).mp ?_
      rwa [Matrix.mulVec_mulVec, hSS, Matrix.one_mulVec]
    have hx' := hx ν hν hνμ ((((S : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) *ᵥ w) hv
    have hcoe : ((((MulEquiv.toMonoidHom (MulAut.conj S)) x :
        ↥(LargeEvenSUGroup (Fin n) K (2 ^ f))) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((x : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
        (((S : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) := by
      simp [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe]
    exact conj_mulVec_eq_inv ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (((x : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) w hSS hx'

end Helpers

section MainProof

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SeitzReduction.UnitaryPilot
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem uni_cube_eigBlock_centerQuot {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) (hn : 4 ≤ n)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {μ : K} (hμ : μ ^ 3 = 1) :
    Nonempty (eigBlock q d μ ⧸ Subgroup.center (eigBlock q d μ) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (Module.finrank K (cubeEigen d μ))) K q)) := by
  classical
  obtain ⟨f, hf1, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst q
  have h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf1
  have hdU : d ∈ primeFormUnitary h (idGram K n) := uni_cube_mem_primeFormUnitary h rfl hd
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨s, τ, hs⟩ :=
    CFSG.StandardType.UnitModel.exists_det_one_conj_diag h Nat.prime_three hq3 hdU hd3
  let D : GL (Fin n) K := SectionRank.OddCover.diagHom n τ
  have hD3 : D ^ 3 = 1 := by
    have hc : D = MulAut.conj (((s : GL (Fin n) K))⁻¹) d := by
      rw [MulAut.conj_apply, inv_inv]; exact hs.symm
    rw [hc, ← map_pow, hd3, map_one]
  have hτ : ∀ i, (τ i : K) ^ 3 = 1 := by
    intro i
    have hD3' : SectionRank.OddCover.diagHom n (τ ^ 3) = 1 := by
      rw [map_pow]; exact hD3
    have hm := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hD3'
    rw [SectionRank.OddCover.coe_diagHom, Units.val_one] at hm
    have hii := congrFun (congrFun hm i) i
    simpa [Pi.pow_apply, Units.val_pow_eq_pow_val] using hii
  let S : ↥(LargeEvenSUGroup (Fin n) K (2 ^ f)) := s
  have hs' : (S : GL (Fin n) K) * D * (S : GL (Fin n) K)⁻¹ = d := by
    show (s : GL (Fin n) K) * D * (s : GL (Fin n) K)⁻¹ = d
    rw [show D = SectionRank.OddCover.diagHom n τ from rfl, ← hs]
    group
  have hfin : Module.finrank K (cubeEigen d μ) = Module.finrank K (cubeEigen D μ) :=
    finrank_cubeEigen_conj hs' μ
  have hblock : eigBlock (2 ^ f) d μ = (eigBlock (2 ^ f) D μ).map
      (MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) S)).toMonoidHom := by
    have hd1 : eigBlock (2 ^ f) d μ = (eigSub (2 ^ f) d μ).map
        (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))) := rfl
    have hD1 : eigBlock (2 ^ f) D μ = (eigSub (2 ^ f) D μ).map
        (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))) := rfl
    have hcomp : (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))).comp
        (MulAut.conj S).toMonoidHom =
        (MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) S)).toMonoidHom.comp
          (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))) := by
      ext g
      change (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))) (S * g * S⁻¹) =
        (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))) S *
          (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))) g *
          ((LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f))) S)⁻¹
      rw [map_mul, map_mul, map_inv]
    rw [hd1, hD1, eigSub_conj S D d hs' μ, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  obtain ⟨eD⟩ := diag_centerQuot h τ hτ hn μ
  rw [hblock, hfin]
  exact ⟨(quotientCenterMapEquiv
    (MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)) S))
    (eigBlock (2 ^ f) D μ)).trans eD⟩

end MainProof

end CFSG.StandardType.TablePThreeKG

end
