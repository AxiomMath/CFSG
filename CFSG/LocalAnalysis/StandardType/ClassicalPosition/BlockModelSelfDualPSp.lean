module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp6
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLSp
public import CFSG.RankThree.PartTwo.Sec21.Item223Of
public import CFSG.Timmesfeld.Transvection.ModelRadical
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSpRoot
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoRootConversePSp
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.PLayer.Bootstrap
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Glue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks2
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import CFSG.RankThree.PartTwo.Sec21.Item226Steps
public import CFSG.RankThree.PartTwo.Sec21.Item229
public import CFSG.Timmesfeld.Transvection.ModelPoints
public import Certificates.Certificate41501

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

open scoped Matrix

private noncomputable abbrev bmSDS_J (n f : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
  Matrix.fromBlocks 0 1 (-1) 0

private noncomputable abbrev bmSDS_A {n f : ℕ} (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) :
    Subalgebra (GaloisField 2 f) (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
  Algebra.adjoin (GaloisField 2 f) (Units.val '' S)

private noncomputable abbrev bmSDS_Ge {n f : ℕ} (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :
    Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) :=
  glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e

private noncomputable abbrev bmSDS_B (n f : ℕ) :
    LinearMap.BilinForm (GaloisField 2 f) ((Fin n ⊕ Fin n) → GaloisField 2 f) :=
  Matrix.toBilin' (bmSDS_J n f)

private noncomputable abbrev bmSDS_W {n f : ℕ}
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :
    Submodule (GaloisField 2 f) ((Fin n ⊕ Fin n) → GaloisField 2 f) :=
  LinearMap.range (Matrix.mulVecLin e)

private theorem bmSDS_ae_eq_smul_e
    {n f : ℕ} (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hdeg : blockDegree (bmSDS_A S) e < 2) :
    ∀ a ∈ bmSDS_A S, ∃ c : GaloisField 2 f, a * e = c • e := by
  intro a ha
  let A : Subalgebra (GaloisField 2 f)
      (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
  let B : Submodule (GaloisField 2 f)
      (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight (GaloisField 2 f) e)
  have heA : e ∈ A := he.1
  have heid : e * e = e := he.2.1
  have hene : e ≠ 0 := he.2.2.1
  have heB : e ∈ B := by
    change e ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight (GaloisField 2 f) e)
    exact ⟨e, heA, by rw [LinearMap.mulRight_apply, heid]⟩
  have haeB : a * e ∈ B := by
    change a * e ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight (GaloisField 2 f) e)
    exact ⟨a, ha, rfl⟩
  have hdegB : Module.finrank (GaloisField 2 f) B < 2 := hdeg
  have hle : B ≤ Submodule.span (GaloisField 2 f) {e} := by
    intro x hx
    by_contra hxspan
    have hli : LinearIndependent (GaloisField 2 f) ![e, x] := by
      rw [LinearIndependent.pair_iff]
      intro c d hcd
      have hd : d = 0 := by
        by_contra hd
        apply hxspan
        have hx' : x = (-(d⁻¹ * c)) • e := by
          have h1 : d⁻¹ • (c • e + d • x) = 0 := by rw [hcd, smul_zero]
          rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hd, one_smul] at h1
          rw [eq_neg_of_add_eq_zero_right h1, neg_smul]
        rw [hx']
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e))
      subst hd
      simp only [zero_smul, add_zero] at hcd
      refine ⟨?_, rfl⟩
      by_contra hc
      have h0 : e = 0 := (smul_eq_zero.mp hcd).resolve_left hc
      exact hene h0
    have hspan_le : Submodule.span (GaloisField 2 f) (Set.range ![e, x]) ≤ B := by
      rw [Submodule.span_le]
      rintro y ⟨k, rfl⟩
      fin_cases k
      · simpa using heB
      · simpa using hx
    have hfin2 : Module.finrank (GaloisField 2 f)
        (Submodule.span (GaloisField 2 f) (Set.range ![e, x])) = 2 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    have hle2 : 2 ≤ Module.finrank (GaloisField 2 f) B :=
      hfin2.ge.trans (Submodule.finrank_mono hspan_le)
    omega
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hle haeB)
  exact ⟨c, hc.symm⟩

private lemma bmSDS_neg_one_matrix_eq_one {ι F : Type} [DecidableEq ι] [Field F] [CharP F 2] :
    (-1 : Matrix ι ι F) = 1 := by
  ext i j
  rw [Matrix.neg_apply, CharTwo.neg_eq]

private lemma bmSDS_J_mul_self {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, zero_add,
    add_zero, Matrix.mul_neg, neg_zero]
  rw [bmSDS_neg_one_matrix_eq_one, Matrix.fromBlocks_one]

private lemma bmSDS_J_transpose {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, bmSDS_neg_one_matrix_eq_one]

private lemma bmSDS_J_det_ne_zero (n f : ℕ) : (bmSDS_J n f).det ≠ 0 :=
  isUnit_iff_ne_zero.mp
    (Matrix.isUnit_det_of_right_inverse (bmSDS_J_mul_self (n := n) (F := GaloisField 2 f)))

private lemma bmSDS_B_nondegenerate (n f : ℕ) : (bmSDS_B n f).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' (bmSDS_J n f)
    (bmSDS_J_det_ne_zero n f)

private lemma bmSDS_B_symm (n f : ℕ) (x y : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    bmSDS_B n f x y = bmSDS_B n f y x := by
  simp only [bmSDS_B, Matrix.toBilin'_apply']
  calc x ⬝ᵥ bmSDS_J n f *ᵥ y
      = x ᵥ* bmSDS_J n f ⬝ᵥ y := by rw [Matrix.dotProduct_mulVec]
    _ = ((bmSDS_J n f)ᵀ *ᵥ x) ⬝ᵥ y := by rw [← Matrix.mulVec_transpose]
    _ = (bmSDS_J n f *ᵥ x) ⬝ᵥ y := by rw [bmSDS_J_transpose]
    _ = y ⬝ᵥ bmSDS_J n f *ᵥ x := by rw [dotProduct_comm]

private lemma bmSDS_B_refl (n f : ℕ) : (bmSDS_B n f).IsRefl :=
  LinearMap.IsSymm.isRefl (LinearMap.IsSymm.mk (fun x y => bmSDS_B_symm n f x y))

private lemma bmSDS_transpose_mul_J {n f : ℕ}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e) :
    eᵀ * bmSDS_J n f = bmSDS_J n f * e := by
  have hdet : IsUnit (bmSDS_J n f).det := isUnit_iff_ne_zero.mpr (bmSDS_J_det_ne_zero n f)
  have h : (bmSDS_J n f)⁻¹ * eᵀ * bmSDS_J n f = e := by
    simpa [formAdj, Matrix.map_id] using hadj
  calc eᵀ * bmSDS_J n f
      = 1 * (eᵀ * bmSDS_J n f) := (Matrix.one_mul _).symm
    _ = ((bmSDS_J n f) * (bmSDS_J n f)⁻¹) * (eᵀ * bmSDS_J n f) := by
          rw [Matrix.mul_nonsing_inv _ hdet]
    _ = bmSDS_J n f * ((bmSDS_J n f)⁻¹ * eᵀ * bmSDS_J n f) := by noncomm_ring
    _ = bmSDS_J n f * e := by rw [h]

private lemma bmSDS_B_self_adjoint {n f : ℕ}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (x y : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    bmSDS_B n f (e *ᵥ x) y = bmSDS_B n f x (e *ᵥ y) := by
  have h7 := bmSDS_transpose_mul_J hadj
  simp only [bmSDS_B, Matrix.toBilin'_apply']
  calc (e *ᵥ x) ⬝ᵥ bmSDS_J n f *ᵥ y
      = (e *ᵥ x) ᵥ* bmSDS_J n f ⬝ᵥ y := by rw [Matrix.dotProduct_mulVec]
    _ = (x ᵥ* (eᵀ * bmSDS_J n f)) ⬝ᵥ y := by rw [Matrix.vecMul_mulVec]
    _ = (x ᵥ* (bmSDS_J n f * e)) ⬝ᵥ y := by rw [h7]
    _ = ((x ᵥ* bmSDS_J n f) ᵥ* e) ⬝ᵥ y := by rw [← Matrix.vecMul_vecMul]
    _ = (x ᵥ* bmSDS_J n f) ⬝ᵥ e *ᵥ y := by rw [← Matrix.dotProduct_mulVec]
    _ = x ⬝ᵥ bmSDS_J n f *ᵥ (e *ᵥ y) := by rw [← Matrix.dotProduct_mulVec]

private lemma bmSDS_B_one_sub {n f : ℕ}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (x y : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    bmSDS_B n f x ((1 - e) *ᵥ y) = bmSDS_B n f ((1 - e) *ᵥ x) y := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    map_sub, map_sub, LinearMap.sub_apply]
  rw [bmSDS_B_self_adjoint hadj x y]

private lemma bmSDS_mulVecLin_idem {n f : ℕ}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hid : IsIdempotentElem e) : IsIdempotentElem (Matrix.mulVecLin e) := by
  show Matrix.mulVecLin e ∘ₗ Matrix.mulVecLin e = Matrix.mulVecLin e
  rw [← Matrix.mulVecLin_mul, hid.eq]

private lemma bmSDS_mulVecLin_add {n f : ℕ}
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :
    Matrix.mulVecLin e + Matrix.mulVecLin (1 - e) =
      (LinearMap.id : ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
        ((Fin n ⊕ Fin n) → GaloisField 2 f)) := by
  rw [← Matrix.mulVecLin_add, add_sub_cancel, Matrix.mulVecLin_one]

private lemma bmSDS_ker_e_eq_range_one_sub {n f : ℕ}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hid : IsIdempotentElem e) :
    LinearMap.ker (Matrix.mulVecLin e) = LinearMap.range (Matrix.mulVecLin (1 - e)) := by
  have hE : IsIdempotentElem (Matrix.mulVecLin e) := bmSDS_mulVecLin_idem hid
  have h := LinearMap.IsIdempotentElem.ker_eq_range_one_sub hE
  have hsub : Matrix.mulVecLin (1 - e) = 1 - Matrix.mulVecLin e := by
    rw [eq_sub_iff_add_eq, add_comm, bmSDS_mulVecLin_add e]
    rfl
  rw [h, hsub]

private lemma bmSDS_isCompl_W {n f : ℕ}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hid : IsIdempotentElem e) :
    IsCompl (bmSDS_W e) (bmSDS_W (1 - e)) := by
  have hE : IsIdempotentElem (Matrix.mulVecLin e) := bmSDS_mulVecLin_idem hid
  have h := LinearMap.IsIdempotentElem.isCompl hE
  rw [bmSDS_ker_e_eq_range_one_sub hid] at h
  exact h

private lemma bmSDS_orthogonal_W {n f : ℕ}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hid : IsIdempotentElem e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e) :
    (bmSDS_B n f).orthogonal (bmSDS_W e) = bmSDS_W (1 - e) := by
  apply le_antisymm
  · intro m hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm
    have hEm : Matrix.mulVecLin e m = 0 := by
      apply (bmSDS_B_nondegenerate n f).2
      intro y
      have h1 : bmSDS_B n f (e *ᵥ y) m = 0 :=
        hm (e *ᵥ y) (LinearMap.mem_range.mpr ⟨y, by rw [Matrix.mulVecLin_apply]⟩)
      rw [bmSDS_B_self_adjoint hadj y m] at h1
      exact h1
    have hEm' : e *ᵥ m = 0 := by rwa [Matrix.mulVecLin_apply] at hEm
    rw [bmSDS_W]
    refine LinearMap.mem_range.mpr ⟨m, ?_⟩
    rw [Matrix.mulVecLin_apply]
    have hm_eq : m = (1 - e) *ᵥ m := by
      calc m = 1 *ᵥ m := (Matrix.one_mulVec m).symm
        _ = (e + (1 - e)) *ᵥ m := by rw [add_sub_cancel]
        _ = e *ᵥ m + (1 - e) *ᵥ m := by rw [Matrix.add_mulVec]
        _ = 0 + (1 - e) *ᵥ m := by rw [hEm']
        _ = (1 - e) *ᵥ m := zero_add _
    exact hm_eq.symm
  · intro m hm
    rw [bmSDS_W] at hm
    obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [bmSDS_W] at hn
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hn
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [bmSDS_B_self_adjoint hadj a ((1 - e) *ᵥ b)]
    have h2 : e *ᵥ ((1 - e) *ᵥ b) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hid.eq, sub_self,
        Matrix.zero_mulVec]
    rw [h2]
    exact map_zero _

private lemma bmSDS_orthogonal_W' {n f : ℕ}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hid : IsIdempotentElem e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e) :
    (bmSDS_B n f).orthogonal (bmSDS_W (1 - e)) = bmSDS_W e := by
  apply le_antisymm
  · intro m hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm
    have h1em : (1 - e) *ᵥ m = 0 := by
      apply (bmSDS_B_nondegenerate n f).2
      intro y
      rw [bmSDS_B_one_sub hadj y m]
      exact hm ((1 - e) *ᵥ y)
        (LinearMap.mem_range.mpr ⟨y, by rw [Matrix.mulVecLin_apply]⟩)
    have hm_eq : m = e *ᵥ m := by
      calc m = 1 *ᵥ m := (Matrix.one_mulVec m).symm
        _ = (e + (1 - e)) *ᵥ m := by rw [add_sub_cancel]
        _ = e *ᵥ m + (1 - e) *ᵥ m := by rw [Matrix.add_mulVec]
        _ = e *ᵥ m + 0 := by rw [h1em]
        _ = e *ᵥ m := add_zero _
    rw [bmSDS_W]
    exact LinearMap.mem_range.mpr ⟨m, by rw [Matrix.mulVecLin_apply]; exact hm_eq.symm⟩
  · intro m hm
    rw [bmSDS_W] at hm
    obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [bmSDS_W] at hn
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hn
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    rw [bmSDS_B_symm n f ((1 - e) *ᵥ a) (e *ᵥ b)]
    rw [bmSDS_B_self_adjoint hadj b ((1 - e) *ᵥ a)]
    have h2 : e *ᵥ ((1 - e) *ᵥ a) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hid.eq, sub_self,
        Matrix.zero_mulVec]
    rw [h2]
    exact map_zero _

private theorem bmSDS_block_decomp
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e) :
    IsCompl (bmSDS_W e) (bmSDS_W (1 - e)) ∧
      (bmSDS_B n f).orthogonal (bmSDS_W e) = bmSDS_W (1 - e) ∧
      (bmSDS_B n f).orthogonal (bmSDS_W (1 - e)) = bmSDS_W e ∧
      ((bmSDS_B n f).restrict (bmSDS_W e)).Nondegenerate ∧
      ((bmSDS_B n f).restrict (bmSDS_W (1 - e))).Nondegenerate := by
  have hid : IsIdempotentElem e := he.2.1
  refine ⟨bmSDS_isCompl_W hid, bmSDS_orthogonal_W hid hadj, bmSDS_orthogonal_W' hid hadj, ?_, ?_⟩
  · exact LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal (bmSDS_B n f)
      (bmSDS_B_refl n f)
      (by rw [bmSDS_orthogonal_W hid hadj]; exact (bmSDS_isCompl_W hid).disjoint)
  · exact LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal (bmSDS_B n f)
      (bmSDS_B_refl n f)
      (by rw [bmSDS_orthogonal_W' hid hadj]; exact (bmSDS_isCompl_W hid).symm.disjoint)

private lemma bmSDS_B_isAlt (n f : ℕ) : (bmSDS_B n f).IsAlt := by
  intro v
  simp only [bmSDS_B, Matrix.toBilin'_apply']
  rw [bmSDS_J, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, bmSDS_neg_one_matrix_eq_one, zero_add,
    add_zero]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
  have hcomm : (∑ i, v (Sum.inl i) * v (Sum.inr i)) =
      ∑ i, v (Sum.inr i) * v (Sum.inl i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  rw [hcomm]
  exact CharTwo.add_self_eq_zero _

private lemma bmSDS_formAdj_one_sub {n f : ℕ}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e) :
    formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) (1 - e) = 1 - e := by
  have hdet : IsUnit (bmSDS_J n f).det := isUnit_iff_ne_zero.mpr (bmSDS_J_det_ne_zero n f)
  have h := Geo.formAdj_add (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) (1 - e) e
  rw [sub_add_cancel, Geo.formAdj_one (RingHom.id (GaloisField 2 f)) hdet, hadj] at h
  exact eq_sub_iff_add_eq.mpr h.symm

private lemma bmSDS_adjoin_comm {n f : ℕ} (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ bmSDS_A S, ∀ b ∈ bmSDS_A S, a * b = b * a := by
  intro a ha b hb
  exact Algebra.adjoin_induction₂ (R := GaloisField 2 f)
    (A := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (s := Units.val '' S)
    (p := fun a b _ _ => a * b = b * a)
    (fun x y hx hy => by
      rcases hx with ⟨s, hs, rfl⟩
      rcases hy with ⟨s', hs', rfl⟩
      simpa only [Units.val_mul] using congrArg
        (fun u : GL (Fin n ⊕ Fin n) (GaloisField 2 f) =>
          (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) (hS s hs s' hs'))
    (fun r₁ r₂ => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, mul_comm])
    (fun r x hx => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    (fun r x hx => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    (fun x y z hx hy hz hxz hyz => by rw [add_mul, mul_add, hxz, hyz])
    (fun x y z hx hy hz hxy hxz => by rw [mul_add, add_mul, hxy, hxz])
    (fun x y z hx hy hz hxz hyz => by
      rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc])
    (fun x y z hx hy hz hxy hxz => by
      rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc]) (x := a) (y := b) ha hb

private lemma bmSDS_commute_e {n f : ℕ}
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hg : g ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hgfix : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) = 1 - e) :
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e =
      e * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
  have hdet : IsUnit (bmSDS_J n f).det := isUnit_iff_ne_zero.mpr (bmSDS_J_det_ne_zero n f)
  have hJh : Matrix.transpose ((bmSDS_J n f).map (RingHom.id (GaloisField 2 f))) = bmSDS_J n f := by
    simpa [Matrix.map_id] using bmSDS_J_transpose (n := n) (F := GaloisField 2 f)
  have hgiso : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f)
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      ((g⁻¹ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    Geo.formAdj_eq_inv_of_isometry (RingHom.id (GaloisField 2 f)) hdet g
      (by simpa [Matrix.map_id] using (CFSG.Open.StatedAPI.mem_statedSp_iff).mp hg)
  have h1e : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) (1 - e) = 1 - e :=
    bmSDS_formAdj_one_sub hadj
  have hginv : ((g⁻¹ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) = 1 - e := by
    have h := congrArg (fun m => ((g⁻¹ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * m) hgfix
    simpa [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      using h.symm
  have hzero : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f)
      ((1 - e) * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e) = 0 := by
    rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hdet,
      Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hdet, hadj, hgiso, h1e, hginv,
      Matrix.mul_sub, Matrix.mul_one, he.2.1, sub_self]
  have hzero' : (1 - e) *
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e = 0 := by
    have h := congrArg (formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f)) hzero
    rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun _ => rfl) hdet hJh] at h
    simpa [formAdj] using h
  have h1e1e : (1 - e) * (1 - e) = 1 - e := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, he.2.1, sub_self,
      sub_zero]
  have hge : (1 - e) * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = 1 - e := by
    calc (1 - e) * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        = (1 - e) * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
            (e + (1 - e)) := by rw [add_sub_cancel, Matrix.mul_one]
      _ = (1 - e) * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e +
            (1 - e) * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
              (1 - e) := by rw [Matrix.mul_add]
      _ = 0 + (1 - e) * ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
            (1 - e)) := by rw [hzero', Matrix.mul_assoc]
      _ = 0 + (1 - e) * (1 - e) := by rw [hgfix]
      _ = 1 - e := by rw [h1e1e, zero_add]
  have hge' : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e =
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - (1 - e) := by
    conv_lhs => rw [show e = 1 - (1 - e) by abel]
    rw [Matrix.mul_sub, Matrix.mul_one, hgfix]
  have heg' : e * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - (1 - e) := by
    conv_lhs => rw [show e = 1 - (1 - e) by abel]
    rw [Matrix.sub_mul, Matrix.one_mul, hge]
  exact hge'.trans heg'.symm

private lemma bmSDS_fixing_le_centralizer {n f : ℕ}
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2)
    (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hg : g ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hgfix : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) = 1 - e) :
    g ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  apply Units.ext
  simp only [Units.val_mul]
  have hge : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e =
      e * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    bmSDS_commute_e S he hadj g hg hgfix
  have hsA : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ bmSDS_A S :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  obtain ⟨c, hse⟩ := bmSDS_ae_eq_smul_e S he hdeg _ hsA
  have hese : e * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e :=
    bmSDS_adjoin_comm S hS e he.1 _ hsA
  have hs1e : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) =
      (1 - e) * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hese, hse]
  have hgse : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
      ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e)) =
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) := by
    rw [hs1e, ← Matrix.mul_assoc, hgfix, ← hs1e]
  have hL : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      c • (e * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) +
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) := by
    calc (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
          (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        = (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
            ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
              (e + (1 - e))) := by rw [add_sub_cancel, Matrix.mul_one]
      _ = (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
              ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e) +
            (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
              ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e)) := by
            rw [Matrix.mul_add, Matrix.mul_add]
      _ = (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (c • e) +
            (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) := by
            rw [hse, hgse]
      _ = c • ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e) +
            (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) := by
            rw [Matrix.mul_smul]
      _ = c • (e * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) +
            (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) := by
            rw [hge]
  have hR : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      c • (e * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) +
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) := by
    calc (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
          (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        = (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
            ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
              (e + (1 - e))) := by rw [add_sub_cancel, Matrix.mul_one]
      _ = (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
              ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e) +
            (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
              ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e)) := by
            rw [Matrix.mul_add, Matrix.mul_add]
      _ = (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
              (e * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) +
            (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) := by
            rw [hge, hgfix]
      _ = ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e) *
              (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) +
            (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) := by
            rw [Matrix.mul_assoc]
      _ = (c • e) * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) +
            (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) := by
            rw [hse]
      _ = c • (e * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) +
            (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) := by
            rw [Matrix.smul_mul]
  rw [hR, hL]

private lemma bmSDS_glFixing_iff_pointwiseStab {n f : ℕ}
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (g : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
    ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) = 1 - e) ↔
      ((CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
        (GaloisField 2 f)) g) ∈ CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
          (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup
            (CFSG.RankThree.SubgroupLists.spForm n (GaloisField 2 f)))
          (bmSDS_W (1 - e)) := by
  rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.mem_pointwiseStab]
  constructor
  · intro hfix u hu
    rw [bmSDS_W] at hu
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hu
    rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hfix]
  · intro h
    refine Matrix.mulVec_injective ?_
    funext x
    have hx := h ((1 - e) *ᵥ x)
      (LinearMap.mem_range.mpr ⟨x, by rw [Matrix.mulVecLin_apply]⟩)
    rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup_apply] at hx
    simpa only [Matrix.mulVec_mulVec] using hx

private lemma bmSDS_map_Ge_eq_pointwiseStab (n f : ℕ)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2) :
    (bmSDS_Ge S e).map
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
          (GaloisField 2 f)).toMonoidHom =
      CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup
          (CFSG.RankThree.SubgroupLists.spForm n (GaloisField 2 f)))
        (bmSDS_W (1 - e)) := by
  apply le_antisymm
  · intro h hh
    rw [Subgroup.mem_map] at hh
    obtain ⟨g, hg, rfl⟩ := hh
    rw [bmSDS_Ge, glBlockCentralizer, Subgroup.mem_comap] at hg
    exact (bmSDS_glFixing_iff_pointwiseStab e g).mp hg.2
  · intro h hh
    obtain ⟨g, hg⟩ :=
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
        (GaloisField 2 f)).surjective h
    have hh' : (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
        (GaloisField 2 f)) g ∈ CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
          (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup
            (CFSG.RankThree.SubgroupLists.spForm n (GaloisField 2 f)))
          (bmSDS_W (1 - e)) := by
      rw [hg]
      exact hh
    rw [Subgroup.mem_map]
    refine ⟨g, ?_, hg⟩
    rw [bmSDS_Ge, glBlockCentralizer, Subgroup.mem_comap]
    exact ⟨bmSDS_fixing_le_centralizer S hS he hadj hdeg g g.2
        ((bmSDS_glFixing_iff_pointwiseStab e g).mpr hh'),
      (bmSDS_glFixing_iff_pointwiseStab e g).mpr hh'⟩

section
open CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCOrthogonal

private noncomputable def bmSDS_restrictPointwise {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {B : LinearMap.BilinForm F V}
    {U : Submodule F V}
    (g : pointwiseStab (linIsometryGroup B) U) :
    bilinIsometryGroup (B.restrict (B.orthogonal U)) := by
  have hfix : ∀ u ∈ U, ((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) u = u :=
    fun u hu => mem_pointwiseStab.mp g.2 u hu
  have hfixinv : ∀ u ∈ U, (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ u = u :=
    fun u hu => mem_pointwiseStab.mp (Subgroup.inv_mem _ g.2) u hu
  have hmem : (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ ∈ linIsometryGroup B :=
    Subgroup.inv_mem _ g.1.2
  have hgiso := mem_linIsometryGroup.mp g.1.2
  have hginviso := mem_linIsometryGroup.mp hmem
  refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv
    (restrictEquiv (B.orthogonal U) (g : V ≃ₗ[F] V) ?_ ?_), ?_⟩
  · intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro u hu
    calc B u (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) x)
        = B ((((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ u)
            ((((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹
              (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) x)) :=
          (hginviso u (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) x)).symm
      _ = B u x := by
        rw [hfixinv u hu]
        exact congrArg (fun z => B u z) ((↑↑(g : ↥(linIsometryGroup B)) :
          V ≃ₗ[F] V).symm_apply_apply x)
      _ = 0 := hx u hu
  · intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro u hu
    calc B u ((((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ x)
        = B (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V) u)
            (((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V)
              ((((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ x)) :=
          (hgiso u ((((g : ↥(linIsometryGroup B)) : V ≃ₗ[F] V))⁻¹ x)).symm
      _ = B u x := by
        rw [hfix u hu]
        exact congrArg (fun z => B u z) ((↑↑(g : ↥(linIsometryGroup B)) :
          V ≃ₗ[F] V).apply_symm_apply x)
      _ = 0 := hx u hu
  · rw [mem_bilinIsometryGroup]
    intro x y
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply, LinearMap.domRestrict_apply]
    simp only [LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, coe_restrictEquiv]
    exact hgiso x y

private lemma bmSDS_restrictPointwise_apply {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {B : LinearMap.BilinForm F V}
    {U : Submodule F V}
    (g : pointwiseStab (linIsometryGroup B) U) (x : B.orthogonal U) :
    ((bmSDS_restrictPointwise g :
        LinearMap.GeneralLinearGroup F (B.orthogonal U)) :
        B.orthogonal U →ₗ[F] B.orthogonal U) x = (g : V ≃ₗ[F] V) x :=
  rfl

private noncomputable def bmSDS_pwIso {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {B : LinearMap.BilinForm F V} (hB : B.IsAlt)
    {U : Submodule F V} (hU : (B.restrict U).Nondegenerate) :
    pointwiseStab (linIsometryGroup B) U ≃*
      bilinIsometryGroup (B.restrict (B.orthogonal U)) where
  toFun := bmSDS_restrictPointwise
  invFun := gluePointwise hB hU
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, r, hu⟩ := exists_coe_add_of_isCompl
      (isCompl_orthogonal_of_nondegenerate hB hU) v
    rw [← hu, gluePointwise_apply, map_add, mem_pointwiseStab.mp g.2 (u : V) u.2]
    rfl
  right_inv φ := by
    apply Subtype.ext
    apply Units.ext
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    rw [bmSDS_restrictPointwise_apply]
    rw [show ((x : B.orthogonal U) : V) = ((0 : U) : V) + (x : V) by simp,
      gluePointwise_apply]
    simpa using zero_add ((φ : LinearMap.GeneralLinearGroup F (B.orthogonal U)) x : V)
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    refine LinearMap.ext fun x => ?_
    rfl

private lemma bmSDS_pwIso_symm_apply {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {B : LinearMap.BilinForm F V} (hB : B.IsAlt)
    {U : Submodule F V} (hU : (B.restrict U).Nondegenerate)
    (h : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
      (B.restrict (B.orthogonal U))) (x : B.orthogonal U) :
    (((bmSDS_pwIso hB hU).symm h : CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup B) U) :
        V ≃ₗ[F] V) (x : V) =
      ((((h : LinearMap.GeneralLinearGroup F (B.orthogonal U)) :
        B.orthogonal U →ₗ[F] B.orthogonal U) x : B.orthogonal U) : V) := by
  change ((gluePointwise hB hU h : V ≃ₗ[F] V) (x : V)) = _
  rw [show (x : V) = ((0 : U) : V) + (x : V) by simp]
  rw [gluePointwise_apply]
  simp

private lemma bmSDS_pwIso_cast {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {B : LinearMap.BilinForm F V} (hB : B.IsAlt)
    {U W₂ : Submodule F V} (hU : (B.restrict U).Nondegenerate)
    (horth : B.orthogonal U = W₂) :
    ∃ eps : CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup B) U ≃*
        CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (B.restrict W₂),
      ∀ (h : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (B.restrict W₂)) (x : W₂),
        (((eps.symm h : CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
            (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup B) U) :
            V ≃ₗ[F] V) (x : V)) =
          ((((h : LinearMap.GeneralLinearGroup F W₂) : W₂ →ₗ[F] W₂) x : W₂) : V) := by
  subst horth
  exact ⟨bmSDS_pwIso hB hU, bmSDS_pwIso_symm_apply hB hU⟩

end

private lemma bmSDS_pointwiseStab_equiv_bilin (n f : ℕ)
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hB : (bmSDS_B n f).IsAlt)
    (hnd : ((bmSDS_B n f).restrict (bmSDS_W (1 - e))).Nondegenerate)
    (horth : (bmSDS_B n f).orthogonal (bmSDS_W (1 - e)) = bmSDS_W e) :
    ∃ eps : CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f))
        (bmSDS_W (1 - e)) ≃*
      CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        ((bmSDS_B n f).restrict (bmSDS_W e)),
      ∀ (h : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
          ((bmSDS_B n f).restrict (bmSDS_W e))) (x : bmSDS_W e),
        (((eps.symm h : CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
            (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f))
            (bmSDS_W (1 - e))) : (Fin n ⊕ Fin n → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
              (Fin n ⊕ Fin n → GaloisField 2 f)) (x : (Fin n ⊕ Fin n → GaloisField 2 f))) =
          ((((h : LinearMap.GeneralLinearGroup (GaloisField 2 f) (bmSDS_W e)) :
              bmSDS_W e →ₗ[GaloisField 2 f] bmSDS_W e) x : bmSDS_W e) :
            (Fin n ⊕ Fin n → GaloisField 2 f)) := by
  exact bmSDS_pwIso_cast (B := bmSDS_B n f) hB hnd horth

private lemma bmSDS_center_statedSp_eq_bot (n f : ℕ) :
    Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) = ⊥ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x _ => ?_
    exact Subsingleton.elim x 1
  · exact CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two hn

private lemma bmSDS_source_longRoot
    (m g' : ℕ) (hm : 1 ≤ m) :
    ∃ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ), GGLongRoot (ggU .PSp m g').D β₀ := by
  have hrank : (ggU .PSp m g').D.rank = m := rfl
  obtain ⟨θ, hθ, hmax⟩ :=
    CFSG.StandardType.exists_maxHeight (D := (ggU .PSp m g').D) (by rw [hrank]; omega)
  exact ⟨θ, 1, θ, hθ, hmax, by rw [map_one, Module.End.one_apply]⟩

private lemma bmSDS_conj_one {U : Type} [Group U] :
    (MulAut.conj (1 : U)).toMonoidHom = MonoidHom.id U := by
  ext x
  simp [MulAut.conj]

private lemma bmSDS_longRoot_conj_one_transv
    (m g' : ℕ) (γ₀ : Fin (ggU .PSp m g').D.rank → ℤ)
    (hγ₀ : γ₀ ∈ (ggU .PSp m g').D.roots)
    (hlγ₀ : GGLongRoot (ggU .PSp m g').D γ₀) :
    ∃ v w : (Fin m ⊕ Fin m) → GaloisField 2 g',
      v ⬝ᵥ (Matrix.mulVec ((Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g'))) w) = 1 ∧
      (((ggU .PSp m g').D.rootGroup γ₀).map
          (MulAut.conj (1 : (ggU .PSp m g').K)).toMonoidHom).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
        matTransvGroup v (Matrix.mulVec ((Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g'))) v) ∧
      (((ggU .PSp m g').D.rootGroup (-γ₀)).map
          (MulAut.conj (1 : (ggU .PSp m g').K)).toMonoidHom).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
        matTransvGroup w (Matrix.mulVec ((Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g'))) w) :=
  CFSG.StandardType.LieKnownR2.Geo.exists_matTransvGroup_eq_conj_rootGroup_Sp m
    (GaloisField 2 g') hγ₀ hlγ₀ 1

private lemma bmSDS_fromBlocks_eq_J (m g' : ℕ) :
    (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
      Matrix.J (Fin m) (GaloisField 2 g') := by
  have h : (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
      -Matrix.J (Fin m) (GaloisField 2 g') :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_eq_neg_J
  rw [h]
  ext i j
  rw [Matrix.neg_apply, CharTwo.neg_eq]

private lemma bmSDS_longRoot_eq_matTransvGroup
    (m g' : ℕ) (γ₀ : Fin (ggU .PSp m g').D.rank → ℤ)
    (hγ₀ : γ₀ ∈ (ggU .PSp m g').D.roots)
    (hlγ₀ : GGLongRoot (ggU .PSp m g').D γ₀) :
    ∃ v : (Fin m ⊕ Fin m) → GaloisField 2 g',
      (((ggU .PSp m g').D.rootGroup γ₀).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup v (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v) := by
  obtain ⟨v, -, -, hX, -⟩ := bmSDS_longRoot_conj_one_transv m g' γ₀ hγ₀ hlγ₀
  refine ⟨v, ?_⟩
  rw [bmSDS_conj_one, Subgroup.map_id] at hX
  simpa only [bmSDS_fromBlocks_eq_J] using hX

private lemma bmSDS_weylAction_mem_roots
    {U : Type} [Group U] (D : CFSG.LieType.Universal.UniversalRootDatum U)
    (w : (CFSG.LieType.RootSystem.coxeterMatrix D.isFiniteType).Group)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    ((CFSG.LieType.RootSystem.weylAction D.isFiniteType) w) γ ∈ D.roots :=
  CFSG.LieType.RootSystem.weylAction_mem_roots D.isFiniteType w hγ

private lemma bmSDS_source_rootGroup_transv
    (m g' : ℕ) (β₀ : Fin (ggU .PSp m g').D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSp m g').D β₀) :
    ∃ v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g',
      (((ggU .PSp m g').D.rootGroup β₀).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup v₀
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) := by
  refine bmSDS_longRoot_eq_matTransvGroup m g' β₀ ?_ hlong
  obtain ⟨w, γ₀, hγ₀, _, hβ⟩ := hlong
  rw [hβ]
  exact bmSDS_weylAction_mem_roots (ggU .PSp m g').D w hγ₀

private lemma bmSDS_embedding_source_transv
    (n f m g' : ℕ)
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hT : ∀ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g'),
      (((ggU .PSp m g').D.rootGroup β₀).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup v₀
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) →
      ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f,
        (((ggU .PSp m g').D.rootGroup β₀).map ι).map
            ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v))
    (β₀ : Fin (ggU .PSp m g').D.rank → ℤ)
    (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hv₀ : (((ggU .PSp m g').D.rootGroup β₀).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup v₀
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) :
    ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f,
      ((((ggU .PSp m g').D.rootGroup β₀).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)) =
        matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) := by
  exact hT β₀ v₀ hv₀

private lemma bmSDS_root_transv_pos
    (n f m g' : ℕ)
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hT : ∀ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g'),
      (((ggU .PSp m g').D.rootGroup β₀).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup v₀
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) →
      ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f,
        (((ggU .PSp m g').D.rootGroup β₀).map ι).map
            ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v))
    (β₀ : Fin (ggU .PSp m g').D.rank → ℤ) (hlong : GGLongRoot (ggU .PSp m g').D β₀) :
    ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f,
      (((ggU .PSp m g').D.rootGroup β₀).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) := by
  obtain ⟨v₀, hv₀⟩ := bmSDS_source_rootGroup_transv m g' β₀ hlong
  exact bmSDS_embedding_source_transv n f m g' ι hT
    β₀ v₀ hv₀

private lemma bmSDS_root_transv_neg
    (n f m g' : ℕ)
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (β₀ : Fin (ggU .PSp m g').D.rank → ℤ)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (hneg : ∃ w : (Fin n ⊕ Fin n) → GaloisField 2 f,
      v ⬝ᵥ (Matrix.mulVec (bmSDS_J n f) w) = 1 ∧
      (((ggU .PSp m g').D.rootGroup (-β₀)).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup w (Matrix.mulVec (bmSDS_J n f) w)) :
    ∃ w : (Fin n ⊕ Fin n) → GaloisField 2 f,
      v ⬝ᵥ (Matrix.mulVec (bmSDS_J n f) w) = 1 ∧
      (((ggU .PSp m g').D.rootGroup (-β₀)).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup w (Matrix.mulVec (bmSDS_J n f) w) := by
  exact hneg

private lemma bmSDS_one_le_m
    {n f m g' : ℕ} {S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hrange : ι.range = bmSDS_Ge S e) : 1 ≤ m := by
  by_contra h
  simp only [not_le] at h
  have hm0 : m = 0 := by omega
  subst m
  haveI : Subsingleton (ggU .PSp 0 g').K := by
    change Subsingleton (StatedSp 0 (GaloisField 2 g'))
    infer_instance
  have hbot : bmSDS_Ge S e = ⊥ := by
    rw [← hrange]
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨y, rfl⟩ := hx
    rw [show y = 1 from Subsingleton.elim y 1, map_one]
  have hJbot : J' = ⊥ := by
    rw [← le_bot_iff]
    calc J' ≤ ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆ := hJe.1
      _ = ⊥ := by rw [hbot, Subgroup.commutator_bot_left]
  have hsub : Subsingleton ↥J' := by rw [hJbot]; infer_instance
  haveI : IsSimpleGroup (↥J' ⧸ Subgroup.center ↥J') := hJe.2.2.2
  have hsubq : Subsingleton (↥J' ⧸ Subgroup.center ↥J') :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J')).subsingleton
  obtain ⟨a, b, hab⟩ := Nontrivial.exists_pair_ne (α := ↥J' ⧸ Subgroup.center ↥J')
  exact hab (Subsingleton.elim a b)

private theorem bmSDS_root_transport
    (n f m g' : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hrange : ι.range = bmSDS_Ge S e)
    (hT : ∀ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g'),
      (((ggU .PSp m g').D.rootGroup β₀).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup v₀
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) →
      ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f,
        (((ggU .PSp m g').D.rootGroup β₀).map ι).map
            ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v))
    (hneg : ∀ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ), GGLongRoot (ggU .PSp m g').D β₀ →
      ∀ (v : (Fin n ⊕ Fin n) → GaloisField 2 f),
      (((ggU .PSp m g').D.rootGroup β₀).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) →
      ∃ w : (Fin n ⊕ Fin n) → GaloisField 2 f,
        v ⬝ᵥ (Matrix.mulVec (bmSDS_J n f) w) = 1 ∧
        (((ggU .PSp m g').D.rootGroup (-β₀)).map ι).map
            ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          matTransvGroup w (Matrix.mulVec (bmSDS_J n f) w)) :
    ∃ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ)
      (v w : (Fin n ⊕ Fin n) → GaloisField 2 f),
      GGLongRoot (ggU .PSp m g').D β₀ ∧ v ⬝ᵥ (Matrix.mulVec (bmSDS_J n f) w) = 1 ∧
      (((ggU .PSp m g').D.rootGroup β₀).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) ∧
      (((ggU .PSp m g').D.rootGroup (-β₀)).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup w (Matrix.mulVec (bmSDS_J n f) w) := by
  obtain ⟨β₀, hlong⟩ :=
    bmSDS_source_longRoot m g'
      (bmSDS_one_le_m hJe ι hrange)
  obtain ⟨v, hv⟩ :=
    bmSDS_root_transv_pos n f m g' ι
      hT β₀ hlong
  obtain ⟨w, hvw, hw⟩ :=
    bmSDS_root_transv_neg n f m g' ι β₀ v
      (hneg β₀ hlong v hv)
  exact ⟨β₀, v, w, hlong, hvw, hv, hw⟩

private lemma bmSDS_blockGroup_finrank_pos
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e) :
    0 < Module.finrank (GaloisField 2 f) (bmSDS_W e) := by
  have hne : Matrix.mulVecLin e ≠ 0 := by
    intro h
    apply he.2.2.1
    apply Matrix.mulVec_injective
    ext v x
    have hv := congrArg
      (fun g : ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
        ((Fin n ⊕ Fin n) → GaloisField 2 f) => g v) h
    simpa [Matrix.mulVecLin_apply] using congrFun hv x
  have hW : bmSDS_W e ≠ ⊥ := by
    rw [bmSDS_W]
    intro hbot
    exact hne (LinearMap.range_eq_bot.mp hbot)
  rw [Module.finrank_pos_iff_exists_ne_zero]
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff (bmSDS_W e)).mp hW
  exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩

private lemma bmSDS_blockGroup_finrank_even
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e) :
    Even (Module.finrank (GaloisField 2 f) (bmSDS_W e)) := by
  have hAltW : ((bmSDS_B n f).restrict (bmSDS_W e)).IsAlt := fun x => bmSDS_B_isAlt n f x
  have hndW := (bmSDS_block_decomp n f S he hadj).2.2.2.1
  obtain ⟨m, b, -⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J
    (B := (bmSDS_B n f).restrict (bmSDS_W e)) hAltW hndW
  rw [Module.finrank_eq_card_basis b]
  refine ⟨m, ?_⟩
  simp [Fintype.card_sum]

private lemma bmSDS_blockGroup_dim_two
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e) :
    2 ≤ Module.finrank (GaloisField 2 f)
        ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e))) := by
  have horth := (bmSDS_block_decomp n f S he hadj).2.2.1
  rw [horth]
  have hpos := bmSDS_blockGroup_finrank_pos n f S he
  obtain ⟨k, hk⟩ := bmSDS_blockGroup_finrank_even n f S he hadj
  omega

private lemma bmSDS_blockGroup_card_small (f : ℕ) (hf : f ≤ 1) :
    Nat.card (GaloisField 2 f) = 2 := by
  interval_cases f
  · exact CFSG.RankThree.PartTwo.Sec21.natCard_galoisField_two_zero
  · rw [GaloisField.card (p := 2) (n := 1) (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num

private lemma bmSDS_blockGroup_card_large (f : ℕ) (hf : 2 ≤ f) :
    4 ≤ Nat.card (GaloisField 2 f) := by
  rw [GaloisField.card (p := 2) (n := f) (by omega : f ≠ 0)]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hf

private lemma bmSDS_blockGroup_quasisimple
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2)
    (h2 : 2 ≤ Module.finrank (GaloisField 2 f)
        ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e))))
    (hK : 4 ≤ Nat.card (GaloisField 2 f) ∨
      (Nat.card (GaloisField 2 f) = 3 ∧
        4 ≤ Module.finrank (GaloisField 2 f)
          ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e)))) ∨
      (Nat.card (GaloisField 2 f) = 2 ∧
        6 ≤ Module.finrank (GaloisField 2 f)
          ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e))))) :
    CFSG.Assembly.IsQuasisimple ↥(bmSDS_Ge S e) := by
  have hmap := bmSDS_map_Ge_eq_pointwiseStab n f S hS he hadj hdeg
  have hndW' := (bmSDS_block_decomp n f S he hadj).2.2.2.2
  have hq := CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.isQuasisimple_pointwiseStab
    (B := bmSDS_B n f) (bmSDS_B_isAlt n f) (bmSDS_B_nondegenerate n f) hndW' h2 hK
  have eiso : bmSDS_Ge S e ≃*
      ↥(CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f))
        (bmSDS_W (1 - e))) :=
    (Subgroup.equivMapOfInjective (bmSDS_Ge S e)
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
        (GaloisField 2 f)).toMonoidHom
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
        (GaloisField 2 f)).injective).trans (MulEquiv.subgroupCongr hmap)
  exact (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥(bmSDS_Ge S e)).2.1.mp
    (CFSG.IsQuasisimple.of_mulEquiv eiso hq)

private lemma bmSDS_blockGroup_perfect
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2)
    (h2 : 2 ≤ Module.finrank (GaloisField 2 f)
        ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e))))
    (hK : 4 ≤ Nat.card (GaloisField 2 f) ∨
      (Nat.card (GaloisField 2 f) = 3 ∧
        4 ≤ Module.finrank (GaloisField 2 f)
          ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e)))) ∨
      (Nat.card (GaloisField 2 f) = 2 ∧
        6 ≤ Module.finrank (GaloisField 2 f)
          ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e))))) :
    bmSDS_Ge S e = ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆ := by
  have hq := bmSDS_blockGroup_quasisimple n f S hS he hadj hdeg h2 hK
  have h1 := congrArg (Subgroup.map (bmSDS_Ge S e).subtype) hq.1
  change Subgroup.map (bmSDS_Ge S e).subtype
      ⁅(⊤ : Subgroup ↥(bmSDS_Ge S e)), ⊤⁆ =
    Subgroup.map (bmSDS_Ge S e).subtype ⊤ at h1
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h1
  exact h1.symm

private lemma bmSDS_blockGroup_component
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hq : CFSG.Assembly.IsQuasisimple ↥(bmSDS_Ge S e))
    (hp : bmSDS_Ge S e = ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆) :
    IsComponentOf (bmSDS_Ge S e) ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆ := by
  refine ⟨hp.le, ?_, hq⟩
  rw [← hp]
  exact IsSubnormal.refl _

private lemma bmSDS_component_eq_top
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (hGe : IsComponentOf (bmSDS_Ge S e) ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆) :
    J' = bmSDS_Ge S e := by
  exact CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hJe.2.2 hJe hGe
    le_rfl (hJe.1.trans (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)))

private noncomputable def bmSDS_matN (n f : ℕ) (x : CFSG.Open.StatedSp n (GaloisField 2 f)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
  ((((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f))) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))

private noncomputable def bmSDS_matM
    (m g' : ℕ) (x : (ggU .PSp m g').K) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g') :=
  ((((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype x :
      GL (Fin m ⊕ Fin m) (GaloisField 2 g'))) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g'))

private def bmSDS_IsBlockEmb
    (n f m g' : ℕ)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f)) :
    Prop :=
  Function.Injective iota ∧
  iota.range = bmSDS_Ge S e ∧
  Function.Injective ext ∧
  (∀ v, v ∈ bmSDS_W e ↔ ∃ u, ext u = v) ∧
  (∀ u u', ext (u + u') = ext u + ext u') ∧
  (∀ c u, ext (c • u) = r c • ext u) ∧
  (∀ u u', bmSDS_B n f (ext u) (ext u') =
    r (u ⬝ᵥ Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) u')) ∧
  (∀ g u, Matrix.mulVec (bmSDS_matN n f (iota g)) (ext u) =
    ext (Matrix.mulVec (bmSDS_matM m g' g) u)) ∧
  (∀ g w, w ∈ bmSDS_W (1 - e) → Matrix.mulVec (bmSDS_matN n f (iota g)) w = w) ∧
  (∀ x, ∃ u, ∃ w' ∈ bmSDS_W (1 - e), x = ext u + w') ∧
  (∀ u, ∀ w' ∈ bmSDS_W (1 - e), bmSDS_B n f (ext u) w' = 0)

private lemma bmSDS_statedSp_symm_apply (m : ℕ) (F : Type) [Field F]
    (y : CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup
      (CFSG.RankThree.SubgroupLists.spForm m F)) :
    CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup m F
      ((CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup m F).symm y) =
        y :=
  MulEquiv.apply_symm_apply _ _

private lemma bmSDS_congrLinearEquiv_coe
    {F M N : Type*} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (φ : M ≃ₗ[F] N) (g : LinearMap.GeneralLinearGroup F M) (x : M) :
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv φ g : N →ₗ[F] N) (φ x)) =
      φ ((g : M →ₗ[F] M) x) := by
  simp [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]

private lemma bmSDS_bilin_intertwine
    (n f m : ℕ) {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (φ : bmSDS_W e ≃ₗ[GaloisField 2 f] (Fin m ⊕ Fin m → GaloisField 2 f))
    (eiso : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
      ((bmSDS_B n f).restrict (bmSDS_W e)) ≃* (ggU .PSp m f).K)
    (h : ∀ (g : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        ((bmSDS_B n f).restrict (bmSDS_W e))) (x : bmSDS_W e),
      φ (((g : LinearMap.GeneralLinearGroup (GaloisField 2 f) (bmSDS_W e)) :
          bmSDS_W e →ₗ[GaloisField 2 f] bmSDS_W e) x) =
      Matrix.mulVec (bmSDS_matM m f (eiso g)) (φ x)) :
    ∀ (g : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        ((bmSDS_B n f).restrict (bmSDS_W e))) (x : bmSDS_W e),
      φ (((g : LinearMap.GeneralLinearGroup (GaloisField 2 f) (bmSDS_W e)) :
          bmSDS_W e →ₗ[GaloisField 2 f] bmSDS_W e) x) =
      Matrix.mulVec (bmSDS_matM m f (eiso g)) (φ x) := by
  exact h

private noncomputable def bmSDS_e2 (m : ℕ) (F : Type) [Field F] :
    CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        (CFSG.RankThree.SubgroupLists.spForm m F) ≃*
      CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup
        (CFSG.RankThree.SubgroupLists.spForm m F) :=
  Subgroup.equivMapOfInjective _ _
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin m ⊕ Fin m → F)).injective

private lemma bmSDS_e2_coe (m : ℕ) (F : Type) [Field F]
    (y : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        (CFSG.RankThree.SubgroupLists.spForm m F)) :
    ((bmSDS_e2 m F y : CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup
        (CFSG.RankThree.SubgroupLists.spForm m F)) :
        (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F)) =
      LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin m ⊕ Fin m → F)
        (y : LinearMap.GeneralLinearGroup F (Fin m ⊕ Fin m → F)) :=
  Subgroup.coe_equivMapOfInjective_apply _ _ _ _

private noncomputable def bmSDS_e1 {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (φ : M ≃ₗ[F] N) (B : LinearMap.BilinForm F M)
    (B' : LinearMap.BilinForm F N)
    (hcongr : Subgroup.map (LinearMap.GeneralLinearGroup.congrLinearEquiv φ).toMonoidHom
        (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B) =
      CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B') :
    CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B ≃*
      CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B' :=
  (Subgroup.equivMapOfInjective _ _
    (LinearMap.GeneralLinearGroup.congrLinearEquiv φ).injective).trans
    (MulEquiv.subgroupCongr hcongr)

private lemma bmSDS_e1_coe {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (φ : M ≃ₗ[F] N) (B : LinearMap.BilinForm F M)
    (B' : LinearMap.BilinForm F N)
    (hcongr : Subgroup.map (LinearMap.GeneralLinearGroup.congrLinearEquiv φ).toMonoidHom
        (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B) =
      CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B')
    (g : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B) :
    ((bmSDS_e1 φ B B' hcongr g : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B') :
        LinearMap.GeneralLinearGroup F N) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv φ (g : LinearMap.GeneralLinearGroup F M) := by
  unfold bmSDS_e1
  exact Subgroup.coe_equivMapOfInjective_apply
    (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B)
    (LinearMap.GeneralLinearGroup.congrLinearEquiv φ).toMonoidHom
    (LinearMap.GeneralLinearGroup.congrLinearEquiv φ).injective g

private lemma bmSDS_e21_apply {m : ℕ} {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module F M] (φ : M ≃ₗ[F] (Fin m ⊕ Fin m → F)) (B : LinearMap.BilinForm F M)
    (hcongr : Subgroup.map (LinearMap.GeneralLinearGroup.congrLinearEquiv φ).toMonoidHom
        (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B) =
      CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        (CFSG.RankThree.SubgroupLists.spForm m F))
    (g : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B) (x : M) :
    φ (((g : LinearMap.GeneralLinearGroup F M) : M →ₗ[F] M) x) =
      ((bmSDS_e2 m F (bmSDS_e1 φ B (CFSG.RankThree.SubgroupLists.spForm m F) hcongr g) :
        CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup
          (CFSG.RankThree.SubgroupLists.spForm m F)) :
        (Fin m ⊕ Fin m → F) ≃ₗ[F] (Fin m ⊕ Fin m → F)) (φ x) := by
  rw [bmSDS_e2_coe, bmSDS_e1_coe]
  exact (bmSDS_congrLinearEquiv_coe φ _ x).symm

private lemma bmSDS_bilin_basis_equiv_ext
    (n f : ℕ) {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hAlt : ((bmSDS_B n f).restrict (bmSDS_W e)).IsAlt)
    (hnd : ((bmSDS_B n f).restrict (bmSDS_W e)).Nondegenerate) :
    ∃ (m : ℕ) (φ : bmSDS_W e ≃ₗ[GaloisField 2 f]
        (Fin m ⊕ Fin m → GaloisField 2 f)),
      Module.finrank (GaloisField 2 f) (bmSDS_W e) = m + m ∧
      (∀ x y, (CFSG.RankThree.SubgroupLists.spForm m (GaloisField 2 f)) (φ x) (φ y)
        = ((bmSDS_B n f).restrict (bmSDS_W e)) x y) ∧
      ∃ (eiso : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
          ((bmSDS_B n f).restrict (bmSDS_W e)) ≃* (ggU .PSp m f).K),
        (∀ (g : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
            ((bmSDS_B n f).restrict (bmSDS_W e))) (x : bmSDS_W e),
          φ (((g : LinearMap.GeneralLinearGroup (GaloisField 2 f) (bmSDS_W e)) :
              bmSDS_W e →ₗ[GaloisField 2 f] bmSDS_W e) x) =
          Matrix.mulVec (bmSDS_matM m f (eiso g)) (φ x)) := by
  obtain ⟨m, b, hb⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J
    (B := (bmSDS_B n f).restrict (bmSDS_W e)) hAlt hnd
  have he : ∀ x y, (CFSG.RankThree.SubgroupLists.spForm m (GaloisField 2 f))
      (b.equivFun x) (b.equivFun y) = ((bmSDS_B n f).restrict (bmSDS_W e)) x y := by
    intro x y
    have hgram : CFSG.ClassicalInvolution.Models.SymplecticPairs.gram (GaloisField 2 f) m =
        Matrix.J (Fin m) (GaloisField 2 f) := by
      rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_eq_neg_J]
      ext i j
      rw [Matrix.neg_apply, CharTwo.neg_eq]
    have hR : ((bmSDS_B n f).restrict (bmSDS_W e)) x y =
        (b.equivFun x) ⬝ᵥ (LinearMap.BilinForm.toMatrix b
          ((bmSDS_B n f).restrict (bmSDS_W e))) *ᵥ (b.equivFun y) := by
      rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec (b := b)]
      rfl
    rw [show CFSG.RankThree.SubgroupLists.spForm m (GaloisField 2 f) =
        CFSG.RankThree.Classical.spForm m (GaloisField 2 f) from rfl,
      CFSG.RankThree.Classical.spForm_apply, hgram, hR, hb]
  have hcongr :=
    CFSG.HardMathSupport.Cooperstein.StructureLie.map_bilinIsometryGroup_congrLinearEquiv
      ((bmSDS_B n f).restrict (bmSDS_W e))
      (CFSG.RankThree.SubgroupLists.spForm m (GaloisField 2 f)) b.equivFun he
  let e1 := bmSDS_e1 b.equivFun ((bmSDS_B n f).restrict (bmSDS_W e))
    (CFSG.RankThree.SubgroupLists.spForm m (GaloisField 2 f)) hcongr
  let e2 := bmSDS_e2 m (GaloisField 2 f)
  let e3 : CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup
        (CFSG.RankThree.SubgroupLists.spForm m (GaloisField 2 f)) ≃* (ggU .PSp m f).K :=
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup m
      (GaloisField 2 f)).symm
  let eiso : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        ((bmSDS_B n f).restrict (bmSDS_W e)) ≃* (ggU .PSp m f).K :=
    (e1.trans e2).trans e3
  refine ⟨m, b.equivFun, by rw [Module.finrank_eq_card_basis b]; simp [Fintype.card_sum],
    he, eiso, ?_⟩
  exact bmSDS_bilin_intertwine n f m b.equivFun eiso (by
    intro g x
    have hmat : Matrix.mulVec (bmSDS_matM m f (eiso g)) (b.equivFun x) =
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup m
          (GaloisField 2 f) (eiso g) :
          (Fin m ⊕ Fin m → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
            (Fin m ⊕ Fin m → GaloisField 2 f)) (b.equivFun x) := by
      rw [bmSDS_matM]
      exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup_apply m
        (GaloisField 2 f) (eiso g) (b.equivFun x)).symm
    rw [hmat]
    have hee : eiso g = (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup m
        (GaloisField 2 f)).symm (e2 (e1 g)) := rfl
    rw [hee, bmSDS_statedSp_symm_apply m (GaloisField 2 f)]
    exact bmSDS_e21_apply b.equivFun ((bmSDS_B n f).restrict (bmSDS_W e)) hcongr g x)

private lemma bmSDS_iso_ext_htrans
    (n f m : ℕ)
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (iota : (ggU .PSp m f).K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (φ : bmSDS_W e ≃ₗ[GaloisField 2 f] (Fin m ⊕ Fin m → GaloisField 2 f))
    (hint : ∀ (g : (ggU .PSp m f).K) (x : bmSDS_W e),
      Matrix.mulVec (bmSDS_matN n f (iota g)) (↑x) =
        ↑(φ.symm (Matrix.mulVec (bmSDS_matM m f g) (φ x)))) :
    ∀ (g : (ggU .PSp m f).K) (x : bmSDS_W e),
      Matrix.mulVec (bmSDS_matN n f (iota g)) (↑x) =
        ↑(φ.symm (Matrix.mulVec (bmSDS_matM m f g) (φ x))) := by
  exact hint

private lemma bmSDS_symm_trans_apply {M N P : Type*} [Mul M] [Mul N] [Mul P]
    (e₁ : M ≃* N) (e₂ : N ≃* P) (g : P) :
    (e₁.trans e₂).symm g = e₁.symm (e₂.symm g) := by
  rfl

private lemma bmSDS_equivMap_symm_apply {G H : Type*} [Group G] [Group H]
    (K : Subgroup G) (f : G →* H) (hf : Function.Injective f)
    (y : Subgroup.map f K) :
    f ↑((Subgroup.equivMapOfInjective K f hf).symm y) = ↑y := by
  rw [← Subgroup.coe_equivMapOfInjective_apply K f hf
    ((Subgroup.equivMapOfInjective K f hf).symm y)]
  rw [MulEquiv.apply_symm_apply]

private lemma bmSDS_subgroupCongr_symm_coe {G : Type*} [Group G]
    (K L : Subgroup G) (h : K = L) (y : L) :
    ((MulEquiv.subgroupCongr h).symm y : G) = (y : G) :=
  rfl

private lemma bmSDS_eiso_symm_val
    (n f m : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (eiso : bmSDS_Ge S e ≃* (ggU .PSp m f).K)
    (eps : CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f))
        (bmSDS_W (1 - e)) ≃*
      CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        ((bmSDS_B n f).restrict (bmSDS_W e)))
    (eb : CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        ((bmSDS_B n f).restrict (bmSDS_W e)) ≃* (ggU .PSp m f).K)
    (hmap : (bmSDS_Ge S e).map
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
          (GaloisField 2 f)).toMonoidHom =
      CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup
          (CFSG.RankThree.SubgroupLists.spForm n (GaloisField 2 f)))
        (bmSDS_W (1 - e)))
    (heiso : eiso =
      (Subgroup.equivMapOfInjective (bmSDS_Ge S e)
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
          (GaloisField 2 f)).toMonoidHom
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
          (GaloisField 2 f)).injective).trans
        ((MulEquiv.subgroupCongr hmap).trans (eps.trans eb)))
    (g : (ggU .PSp m f).K) :
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
        (GaloisField 2 f) ((bmSDS_Ge S e).subtype (eiso.symm g)) :
        CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f)) =
      ((eps.symm (eb.symm g) : CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f))
        (bmSDS_W (1 - e))) :
        CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f)) := by
  rw [heiso]
  rw [bmSDS_symm_trans_apply]
  rw [show ((MulEquiv.subgroupCongr hmap).trans (eps.trans eb)).symm g =
      (MulEquiv.subgroupCongr hmap).symm ((eps.trans eb).symm g) from
    bmSDS_symm_trans_apply (MulEquiv.subgroupCongr hmap) (eps.trans eb) g]
  rw [show (eps.trans eb).symm g = eps.symm (eb.symm g) from
    bmSDS_symm_trans_apply eps eb g]
  exact (bmSDS_equivMap_symm_apply (bmSDS_Ge S e)
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
      (GaloisField 2 f)).toMonoidHom
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
      (GaloisField 2 f)).injective
    ((MulEquiv.subgroupCongr hmap).symm (eps.symm (eb.symm g)))).trans
    (bmSDS_subgroupCongr_symm_coe ((bmSDS_Ge S e).map
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
        (GaloisField 2 f)).toMonoidHom)
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
        (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f))
        (bmSDS_W (1 - e))) hmap (eps.symm (eb.symm g)))

private lemma bmSDS_blockGroup_iso_ext
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2) :
    ∃ (m : ℕ) (iota : (ggU .PSp m f).K →* CFSG.Open.StatedSp n (GaloisField 2 f)),
      Function.Injective iota ∧ iota.range = bmSDS_Ge S e ∧
      (∀ y, iota y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
        y ∈ Subgroup.center (ggU .PSp m f).K) ∧
      Module.finrank (GaloisField 2 f) (bmSDS_W e) = m + m ∧
      ∃ (φ : bmSDS_W e ≃ₗ[GaloisField 2 f] (Fin m ⊕ Fin m → GaloisField 2 f)),
        (∀ x y, ((bmSDS_B n f).restrict (bmSDS_W e)) x y =
          (CFSG.RankThree.SubgroupLists.spForm m (GaloisField 2 f)) (φ x) (φ y)) ∧
        (∀ (g : (ggU .PSp m f).K) (x : bmSDS_W e),
          Matrix.mulVec (bmSDS_matN n f (iota g)) (↑x) =
            ↑(φ.symm (Matrix.mulVec (bmSDS_matM m f g) (φ x)))) := by
  obtain ⟨-, horthW, horthW', hndW, hndW'⟩ :=
    bmSDS_block_decomp n f S he hadj
  have hmap := bmSDS_map_Ge_eq_pointwiseStab n f S hS he hadj hdeg
  obtain ⟨eps, heps⟩ := bmSDS_pointwiseStab_equiv_bilin n f
    (bmSDS_B_isAlt n f) hndW' horthW'
  have hAltW : ((bmSDS_B n f).restrict (bmSDS_W e)).IsAlt :=
    fun x => bmSDS_B_isAlt n f x
  obtain ⟨m, φ, hfin, hsp, ⟨eb, hbint⟩⟩ :=
    bmSDS_bilin_basis_equiv_ext n f (e := e) hAltW hndW
  let eiso : bmSDS_Ge S e ≃* (ggU .PSp m f).K :=
    (Subgroup.equivMapOfInjective (bmSDS_Ge S e)
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
        (GaloisField 2 f)).toMonoidHom
      (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
        (GaloisField 2 f)).injective).trans
      ((MulEquiv.subgroupCongr hmap).trans (eps.trans eb))
  refine ⟨m, (bmSDS_Ge S e).subtype.comp eiso.symm.toMonoidHom,
    ?_, ?_, ?_, hfin, φ, ?_, ?_⟩
  · intro x y hxy
    exact eiso.symm.injective (Subgroup.subtype_injective (bmSDS_Ge S e) hxy)
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eiso.symm.surjective]
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  · intro y hy
    rw [bmSDS_center_statedSp_eq_bot] at hy
    rw [Subgroup.mem_bot] at hy
    have h1 : eiso.symm y = 1 :=
      Subgroup.subtype_injective (bmSDS_Ge S e) (by simpa using hy)
    rw [show y = 1 from eiso.symm.injective (by rw [h1, map_one])]
    exact Subgroup.one_mem _
  · intro x y
    simpa using (hsp x y).symm
  · exact bmSDS_iso_ext_htrans n f m
      ((bmSDS_Ge S e).subtype.comp eiso.symm.toMonoidHom) φ (by
        intro g x
        have hb := hbint (eb.symm g) x
        rw [eb.apply_symm_apply] at hb
        rw [show Matrix.mulVec (bmSDS_matM m f g) (φ x) =
            φ (((eb.symm g : LinearMap.GeneralLinearGroup (GaloisField 2 f)
                (bmSDS_W e)) : bmSDS_W e →ₗ[GaloisField 2 f] bmSDS_W e) x)
            from hb.symm]
        rw [φ.symm_apply_apply]
        have hmat : Matrix.mulVec (bmSDS_matN n f (((bmSDS_Ge S e).subtype.comp
            eiso.symm.toMonoidHom) g)) (↑x) =
            (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
              (GaloisField 2 f) ((bmSDS_Ge S e).subtype.comp eiso.symm.toMonoidHom g) :
              (Fin n ⊕ Fin n → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
                (Fin n ⊕ Fin n → GaloisField 2 f)) (↑x) := by
          rw [bmSDS_matN]
          exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup_apply n
            (GaloisField 2 f) ((bmSDS_Ge S e).subtype.comp eiso.symm.toMonoidHom g) (↑x)).symm
        rw [hmat]
        rw [show (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup n
              (GaloisField 2 f) ((bmSDS_Ge S e).subtype.comp eiso.symm.toMonoidHom g) :
              CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f)) =
            ((eps.symm (eb.symm g) : CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.pointwiseStab
              (CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f))
              (bmSDS_W (1 - e))) :
              CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.linIsometryGroup (bmSDS_B n f))
            from bmSDS_eiso_symm_val n f m S eiso eps eb hmap
              rfl g]
        exact heps (eb.symm g) x)

private lemma bmSDS_embedding_compat
    (n f m g' : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (h6 : ∀ g u, Matrix.mulVec (bmSDS_matN n f (iota g)) (ext u) =
      ext (Matrix.mulVec (bmSDS_matM m g' g) u))
    (hcore : (1 ≤ g' ∨ g' = 0) ∧ Function.Injective iota ∧ iota.range = bmSDS_Ge S e ∧
      (∀ y, iota y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
        y ∈ Subgroup.center (ggU .PSp m g').K) ∧
      Function.Injective ext ∧
      (∀ v, v ∈ bmSDS_W e ↔ ∃ u, ext u = v) ∧
      (∀ u u', ext (u + u') = ext u + ext u') ∧
      (∀ c u, ext (c • u) = r c • ext u) ∧
      (∀ u u', bmSDS_B n f (ext u) (ext u') =
        r (u ⬝ᵥ Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) u'))) :
    (∀ g u, Matrix.mulVec (bmSDS_matN n f (iota g)) (ext u) =
      ext (Matrix.mulVec (bmSDS_matM m g' g) u)) ∧
    (∀ g w, w ∈ bmSDS_W (1 - e) →
      Matrix.mulVec (bmSDS_matN n f (iota g)) w = w) ∧
    (∀ x, ∃ u, ∃ w' ∈ bmSDS_W (1 - e), x = ext u + w') ∧
    (∀ u, ∀ w' ∈ bmSDS_W (1 - e), bmSDS_B n f (ext u) w' = 0) := by
  obtain ⟨h1, hi, hr, hc, hext, hv, hadd, hsemi, hiso⟩ := hcore
  obtain ⟨hcompl, horthW, -, -, -⟩ := bmSDS_block_decomp n f S he hadj
  refine ⟨h6, ?_, ?_, ?_⟩
  · intro g w hw
    have hg : iota g ∈ bmSDS_Ge S e := by rw [← hr]; exact ⟨g, rfl⟩
    have hps := (bmSDS_glFixing_iff_pointwiseStab e (iota g)).mp hg.2
    have hfix := CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.mem_pointwiseStab.mp hps w hw
    rw [CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine.statedSpEquivLinIsometryGroup_apply] at hfix
    exact hfix
  · intro x
    have hx : x ∈ (bmSDS_W e) ⊔ (bmSDS_W (1 - e)) := by
      rw [hcompl.sup_eq_top]; trivial
    obtain ⟨w, hw, w', hw', hxw⟩ := Submodule.mem_sup.mp hx
    obtain ⟨u, hu⟩ := (hv w).mp hw
    exact ⟨u, w', hw', by rw [hu]; exact hxw.symm⟩
  · intro u w' hw'
    have hwW : ext u ∈ bmSDS_W e := (hv (ext u)).mpr ⟨u, rfl⟩
    have hmem : w' ∈ (bmSDS_B n f).orthogonal (bmSDS_W e) := by rw [horthW]; exact hw'
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hmem) (ext u) hwW

private lemma bmSDS_matN_coe (n f : ℕ)
    (x : CFSG.Open.StatedSp n (GaloisField 2 f)) :
    bmSDS_matN n f x =
      (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
  rfl

private lemma bmSDS_matM_coe
    (m g' : ℕ) (x : (ggU .PSp m g').K) :
    bmSDS_matM m g' x =
      (((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype x :
        GL (Fin m ⊕ Fin m) (GaloisField 2 g')) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) :=
  rfl

private lemma bmSDS_transv_gen_W_key
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (v₀ u : (Fin m ⊕ Fin m) → GaloisField 2 g') :
    r (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀ ⬝ᵥ u) =
      Matrix.mulVec (bmSDS_J n f) (ext v₀) ⬝ᵥ ext u := by
  have hJtm : (Matrix.J (Fin m) (GaloisField 2 g')).transpose =
      Matrix.J (Fin m) (GaloisField 2 g') := by
    ext i j
    rcases i with a | a <;> rcases j with b | b <;>
      simp [Matrix.J, Matrix.one_apply, CharTwo.neg_eq, eq_comm]
  have hJtn : (bmSDS_J n f).transpose = bmSDS_J n f := by
    ext i j
    rcases i with a | a <;> rcases j with b | b <;>
      simp [bmSDS_J, Matrix.one_apply, CharTwo.neg_eq, eq_comm]
  have hL : (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) ⬝ᵥ u =
      v₀ ⬝ᵥ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) u) := by
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, hJtm]
  have hR : (Matrix.mulVec (bmSDS_J n f) (ext v₀)) ⬝ᵥ ext u =
      bmSDS_B n f (ext v₀) (ext u) := by
    rw [bmSDS_B, Matrix.toBilin'_apply']
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, hJtn]
  have hG := h.2.2.2.2.2.2.1
  rw [hL, hR, ← hG v₀ u]

private lemma bmSDS_transv_gen_W
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (g : (ggU .PSp m g').K) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (c : GaloisField 2 g')
    (hg : ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype g :
        GL (Fin m ⊕ Fin m) (GaloisField 2 g')) =
      1 + c • Matrix.vecMulVec v₀
        (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀))
    (u : (Fin m ⊕ Fin m) → GaloisField 2 g') :
    Matrix.mulVec
        ((((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (iota g) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) (ext u) =
      Matrix.mulVec
        (1 + r c • Matrix.vecMulVec (ext v₀)
          (Matrix.mulVec (bmSDS_J n f) (ext v₀)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (ext u) := by
  have h6 := h.2.2.2.2.2.2.2.1 g u
  rw [bmSDS_matN_coe, bmSDS_matM_coe, hg] at h6
  rw [h6, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec]
  rw [h.2.2.2.2.1, h.2.2.2.2.2.1]
  have hL' : ext (MulOpposite.op ((Matrix.J (Fin m) (GaloisField 2 g')) *ᵥ v₀ ⬝ᵥ u) • v₀) =
      r ((Matrix.J (Fin m) (GaloisField 2 g')) *ᵥ v₀ ⬝ᵥ u) • ext v₀ := by
    rw [IsCentralScalar.op_smul_eq_smul]
    exact h.2.2.2.2.2.1 _ v₀
  have hR' : MulOpposite.op ((bmSDS_J n f) *ᵥ ext v₀ ⬝ᵥ ext u) • ext v₀ =
      r ((Matrix.J (Fin m) (GaloisField 2 g')) *ᵥ v₀ ⬝ᵥ u) • ext v₀ := by
    rw [IsCentralScalar.op_smul_eq_smul]
    rw [← bmSDS_transv_gen_W_key n f m g' r ext S e iota h v₀ u]
  rw [hL', hR']

private lemma bmSDS_transport_rootGroup_gen
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (g : (ggU .PSp m g').K) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (c : GaloisField 2 g')
    (hg : ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype g :
        GL (Fin m ⊕ Fin m) (GaloisField 2 g')) =
      1 + c • Matrix.vecMulVec v₀
        (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) :
    ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (iota g) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + r c • Matrix.vecMulVec (ext v₀)
        (Matrix.mulVec (bmSDS_J n f) (ext v₀)) := by
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨u, w', hw', rfl⟩ := h.2.2.2.2.2.2.2.2.2.1 x
  rw [Matrix.mulVec_add]
  rw [bmSDS_transv_gen_W n f m g' r iota ext S e h g v₀ c hg u]
  rw [← bmSDS_matN_coe, h.2.2.2.2.2.2.2.2.1 g w' hw']
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.smul_mulVec]
  have hJw : (Matrix.mulVec (bmSDS_J n f) (ext v₀)) ⬝ᵥ w' = 0 := by
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
    rw [show (bmSDS_J n f).transpose = bmSDS_J n f from by
      ext i j
      rcases i with a | a <;> rcases j with b | b <;>
        simp [bmSDS_J, Matrix.one_apply, CharTwo.neg_eq, eq_comm]]
    rw [← Matrix.toBilin'_apply']
    exact h.2.2.2.2.2.2.2.2.2.2 v₀ w' hw'
  have hAw : (Matrix.vecMulVec (ext v₀)
      (Matrix.mulVec (bmSDS_J n f) (ext v₀))) *ᵥ w' = 0 := by
    rw [Matrix.vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul, hJw, zero_smul]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec]
  rw [hAw, smul_zero, add_zero]

private lemma bmSDS_transv_image_preimage
    (m g' : ℕ)
    (X : Subgroup (ggU .PSp m g').K) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      matTransvGroup v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) :
    ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype ''
      (((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) ⁻¹'
        {g : GL (Fin m ⊕ Fin m) (GaloisField 2 g') |
          ∃ c : GaloisField 2 g',
            (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
              1 + c • Matrix.vecMulVec v₀
                (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)}))
      = {g : GL (Fin m ⊕ Fin m) (GaloisField 2 g') |
          ∃ c : GaloisField 2 g',
            (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
              1 + c • Matrix.vecMulVec v₀
                (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)} := by
  rw [Set.image_preimage_eq_inter_range]
  exact Set.inter_eq_left.mpr fun y hy => by
    have hy' : y ∈ matTransvGroup v₀
        (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) :=
      Subgroup.subset_closure hy
    rw [← hX] at hy'
    obtain ⟨g, -, rfl⟩ := hy'
    exact ⟨g, rfl⟩

private lemma bmSDS_transv_X_eq_closure'
    (m g' : ℕ)
    (X : Subgroup (ggU .PSp m g').K) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      matTransvGroup v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) :
    X = Subgroup.closure
      (((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) ⁻¹'
        {g : GL (Fin m ⊕ Fin m) (GaloisField 2 g') |
          ∃ c : GaloisField 2 g',
            (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
              1 + c • Matrix.vecMulVec v₀
                (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)}) := by
  have hf : Function.Injective
      ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype :
        (ggU .PSp m g').K →* GL (Fin m ⊕ Fin m) (GaloisField 2 g')) :=
    Subgroup.subtype_injective _
  apply Subgroup.map_injective hf
  rw [hX, matTransvGroup, MonoidHom.map_closure,
    bmSDS_transv_image_preimage m g' X v₀ hX]

private lemma bmSDS_transv_gen_mem
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (g : (ggU .PSp m g').K) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (c : GaloisField 2 g')
    (hc : ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype g :
        GL (Fin m ⊕ Fin m) (GaloisField 2 g')) =
      1 + c • Matrix.vecMulVec v₀
        (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) :
    ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (iota g) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      matTransvGroup (ext v₀) (Matrix.mulVec (bmSDS_J n f) (ext v₀)) := by
  rw [matTransvGroup]
  refine Subgroup.subset_closure ⟨r c, ?_⟩
  rw [bmSDS_transport_rootGroup_gen n f m g' r iota ext S e h g v₀ c hc]

private lemma bmSDS_transv_mem_closure
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (X : Subgroup (ggU .PSp m g').K) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      matTransvGroup v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀))
    (g : (ggU .PSp m g').K) (hg : g ∈ X) :
    ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (iota g) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      matTransvGroup (ext v₀) (Matrix.mulVec (bmSDS_J n f) (ext v₀)) := by
  rw [bmSDS_transv_X_eq_closure' m g' X v₀ hX] at hg
  refine Subgroup.closure_induction (p := fun y _ =>
      ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (iota y) :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
        matTransvGroup (ext v₀) (Matrix.mulVec (bmSDS_J n f) (ext v₀))) ?_ ?_ ?_ ?_ hg
  · intro y hy
    exact bmSDS_transv_gen_mem n f m g' r iota ext S e h y v₀
      (Set.mem_preimage.mp hy).choose (Set.mem_preimage.mp hy).choose_spec
  · rw [map_one, map_one]; exact one_mem _
  · intro a b ha hb ha' hb'
    rw [map_mul, map_mul]; exact mul_mem ha' hb'
  · intro a ha ha'
    rw [map_inv, map_inv]; exact inv_mem ha'

private lemma bmSDS_vecMulVec_sq_zero (m g' : ℕ)
    (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g') :
    Matrix.vecMulVec v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) *
      Matrix.vecMulVec v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have h0 : (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) ⬝ᵥ v₀ = 0 := by
    rw [dotProduct_comm, ← Matrix.toBilin'_apply', ← bmSDS_fromBlocks_eq_J]
    exact (bmSDS_B_isAlt m g').self_eq_zero v₀
  rw [h0, zero_smul, Matrix.vecMulVec_zero]

private lemma bmSDS_transv_sq_one (m g' : ℕ)
    (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g') (c : GaloisField 2 g') :
    (1 + c • Matrix.vecMulVec v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) *
      (1 + c • Matrix.vecMulVec v₀
        (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) = 1 := by
  have hcc : c + c = 0 := by
    rw [← two_nsmul, nsmul_eq_mul, CharP.cast_eq_zero (GaloisField 2 g') 2, zero_mul]
  have hM := bmSDS_vecMulVec_sq_zero m g' v₀
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM, smul_zero, add_zero]
  rw [add_assoc, ← add_smul, hcc, zero_smul, add_zero]

private lemma bmSDS_transv_source_gen (m g' : ℕ)
    (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g') (c : GaloisField 2 g') :
    ∃ y₀ : GL (Fin m ⊕ Fin m) (GaloisField 2 g'),
      (y₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
        1 + c • Matrix.vecMulVec v₀
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) := by
  refine ⟨(IsUnit.of_mul_eq_one (1 + c • Matrix.vecMulVec v₀
    (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀))
      (bmSDS_transv_sq_one m g' v₀ c)).unit, ?_⟩
  rw [IsUnit.unit_spec]

private lemma bmSDS_transv_image_gens_ge
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (X : Subgroup (ggU .PSp m g').K) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      matTransvGroup v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) :
    {g : GL (Fin n ⊕ Fin n) (GaloisField 2 f) |
          ∃ d : GaloisField 2 f,
            (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
              1 + d • Matrix.vecMulVec (ext v₀)
                (Matrix.mulVec (bmSDS_J n f) (ext v₀))} ⊆
      (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype).comp iota) ''
        ((((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) ⁻¹'
          {g : GL (Fin m ⊕ Fin m) (GaloisField 2 g') |
          ∃ c : GaloisField 2 g',
            (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
              1 + c • Matrix.vecMulVec v₀
                (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)})) := by
  rintro y ⟨d, hd⟩
  obtain ⟨c, rfl⟩ := r.surjective d
  obtain ⟨y₀, hy₀⟩ := bmSDS_transv_source_gen m g' v₀ c
  have hy : y₀ ∈ matTransvGroup v₀
      (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) :=
    Subgroup.subset_closure ⟨c, hy₀⟩
  rw [← hX] at hy
  obtain ⟨g, hg, hgy⟩ := hy
  refine ⟨g, ?_, ?_⟩
  · exact ⟨c, hgy ▸ hy₀⟩
  · apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun ((bmSDS_transport_rootGroup_gen n f m g' r iota ext S e h
      g v₀ c (hgy ▸ hy₀)).trans hd.symm) i) j

private lemma bmSDS_transv_map_le
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (X : Subgroup (ggU .PSp m g').K) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      matTransvGroup v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) :
    X.map (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype).comp iota) ≤
      matTransvGroup (ext v₀) (Matrix.mulVec (bmSDS_J n f) (ext v₀)) := by
  rw [Subgroup.map_le_iff_le_comap]
  intro g hg
  exact bmSDS_transv_mem_closure n f m g' r iota ext S e h X v₀ hX g hg

private lemma bmSDS_transv_ge
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (X : Subgroup (ggU .PSp m g').K) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      matTransvGroup v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) :
    matTransvGroup (ext v₀) (Matrix.mulVec (bmSDS_J n f) (ext v₀)) ≤
      X.map (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype).comp iota) := by
  rw [matTransvGroup, Subgroup.closure_le]
  rintro y ⟨d, hd⟩
  have hy := bmSDS_transv_image_gens_ge n f m g' r iota ext S e h X v₀ hX
    ⟨d, hd⟩
  obtain ⟨g, hg, rfl⟩ := hy
  refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
  have hg' : ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype g) ∈
      X.map ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) := by
    rw [hX]
    exact Subgroup.subset_closure hg
  obtain ⟨g', hg'X, hgg'⟩ := hg'
  rwa [Subtype.coe_injective hgg'] at hg'X

private lemma bmSDS_transport_rootGroup
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (X : Subgroup (ggU .PSp m g').K) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      matTransvGroup v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀)) :
    (X.map iota).map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      matTransvGroup (ext v₀) (Matrix.mulVec (bmSDS_J n f) (ext v₀)) := by
  rw [Subgroup.map_map]
  exact le_antisymm
    (bmSDS_transv_map_le n f m g' r iota ext S e h X v₀ hX)
    (bmSDS_transv_ge n f m g' r iota ext S e h X v₀ hX)

private lemma bmSDS_altSiegel_gen_W
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (g : (ggU .PSp m g').K) (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (c : GaloisField 2 g')
    (hc : ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype g :
        GL (Fin m ⊕ Fin m) (GaloisField 2 g')) =
      1 + c • (Matrix.vecMulVec a₁
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)))
    (u : (Fin m ⊕ Fin m) → GaloisField 2 g') :
    Matrix.mulVec
        ((((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (iota g) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) (ext u) =
      Matrix.mulVec
        (1 + r c • (Matrix.vecMulVec (ext a₁)
            (Matrix.mulVec (bmSDS_J n f) (ext a₂)) +
          Matrix.vecMulVec (ext a₂) (Matrix.mulVec (bmSDS_J n f) (ext a₁))) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (ext u) := by
  have h6 := h.2.2.2.2.2.2.2.1 g u
  rw [bmSDS_matN_coe, bmSDS_matM_coe, hc] at h6
  rw [h6, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  rw [h.2.2.2.2.1, h.2.2.2.2.2.1]
  rw [IsCentralScalar.op_smul_eq_smul, IsCentralScalar.op_smul_eq_smul,
    IsCentralScalar.op_smul_eq_smul, IsCentralScalar.op_smul_eq_smul]
  rw [h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.1]
  rw [bmSDS_transv_gen_W_key n f m g' r ext S e iota h a₂ u,
    bmSDS_transv_gen_W_key n f m g' r ext S e iota h a₁ u]

private lemma bmSDS_altSiegel_gen_W'
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext) (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (c : GaloisField 2 g')
    (w' : (Fin n ⊕ Fin n) → GaloisField 2 f) (hw' : w' ∈ bmSDS_W (1 - e)) :
    Matrix.mulVec
        (1 + r c • (Matrix.vecMulVec (ext a₁)
            (Matrix.mulVec (bmSDS_J n f) (ext a₂)) +
          Matrix.vecMulVec (ext a₂) (Matrix.mulVec (bmSDS_J n f) (ext a₁))) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) w' = w' := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
    IsCentralScalar.op_smul_eq_smul, IsCentralScalar.op_smul_eq_smul]
  have h1 : (Matrix.mulVec (bmSDS_J n f) (ext a₁)) ⬝ᵥ w' = 0 := by
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
    rw [show (bmSDS_J n f).transpose = bmSDS_J n f from by
      ext i j
      rcases i with a | a <;> rcases j with b | b <;>
        simp [bmSDS_J, Matrix.one_apply, CharTwo.neg_eq, eq_comm]]
    rw [← Matrix.toBilin'_apply']
    exact h.2.2.2.2.2.2.2.2.2.2 a₁ w' hw'
  have h2 : (Matrix.mulVec (bmSDS_J n f) (ext a₂)) ⬝ᵥ w' = 0 := by
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
    rw [show (bmSDS_J n f).transpose = bmSDS_J n f from by
      ext i j
      rcases i with a | a <;> rcases j with b | b <;>
        simp [bmSDS_J, Matrix.one_apply, CharTwo.neg_eq, eq_comm]]
    rw [← Matrix.toBilin'_apply']
    exact h.2.2.2.2.2.2.2.2.2.2 a₂ w' hw'
  rw [h1, h2]
  simp

private lemma bmSDS_transport_altSiegel_gen
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (g : (ggU .PSp m g').K) (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (c : GaloisField 2 g')
    (hc : ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype g :
        GL (Fin m ⊕ Fin m) (GaloisField 2 g')) =
      1 + c • (Matrix.vecMulVec a₁
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁))) :
    ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (iota g) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + r c • (Matrix.vecMulVec (ext a₁)
          (Matrix.mulVec (bmSDS_J n f) (ext a₂)) +
        Matrix.vecMulVec (ext a₂) (Matrix.mulVec (bmSDS_J n f) (ext a₁))) := by
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨u, w', hw', rfl⟩ := h.2.2.2.2.2.2.2.2.2.1 x
  rw [Matrix.mulVec_add]
  rw [bmSDS_altSiegel_gen_W n f m g' r iota ext S e h g a₁ a₂ c hc u]
  rw [← bmSDS_matN_coe, h.2.2.2.2.2.2.2.2.1 g w' hw']
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.smul_mulVec,
    Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
    IsCentralScalar.op_smul_eq_smul, IsCentralScalar.op_smul_eq_smul]
  rw [bmSDS_altSiegel_gen_W' n f m g' r iota ext S e h a₁ a₂ c w' hw']
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul, smul_smul]

private lemma bmSDS_altSiegel_image_preimage
    (m g' : ℕ)
    (X : Subgroup (ggU .PSp m g').K)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 g')) a₁ a₂) :
    ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype ''
        (((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) ⁻¹'
          {g : GL (Fin m ⊕ Fin m) (GaloisField 2 g') |
          ∃ c : GaloisField 2 g',
            (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
              1 + c • (Matrix.vecMulVec a₁
                  (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
                Matrix.vecMulVec a₂
                  (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁))})) =
      {g : GL (Fin m ⊕ Fin m) (GaloisField 2 g') |
          ∃ c : GaloisField 2 g',
            (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
              1 + c • (Matrix.vecMulVec a₁
                  (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
                Matrix.vecMulVec a₂
                  (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁))} := by
  rw [Set.image_preimage_eq_inter_range]
  exact Set.inter_eq_left.mpr fun y hy => by
    have hy' : y ∈ altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 g')) a₁ a₂ :=
      Subgroup.subset_closure hy
    rw [← hX] at hy'
    obtain ⟨g, -, rfl⟩ := hy'
    exact ⟨g, rfl⟩

private lemma bmSDS_altSiegel_X_eq_closure'
    (m g' : ℕ)
    (X : Subgroup (ggU .PSp m g').K)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 g')) a₁ a₂) :
    X = Subgroup.closure
      (((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) ⁻¹'
        {g : GL (Fin m ⊕ Fin m) (GaloisField 2 g') |
          ∃ c : GaloisField 2 g',
            (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
              1 + c • (Matrix.vecMulVec a₁
                  (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
                Matrix.vecMulVec a₂
                  (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁))}) := by
  have hf : Function.Injective
      ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype :
        (ggU .PSp m g').K →* GL (Fin m ⊕ Fin m) (GaloisField 2 g')) :=
    Subgroup.subtype_injective _
  apply Subgroup.map_injective hf
  rw [hX, altSiegelGroup, MonoidHom.map_closure,
    bmSDS_altSiegel_image_preimage m g' X a₁ a₂ hX]

private lemma bmSDS_altSiegel_gen_mem
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (y : (ggU .PSp m g').K) (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (c : GaloisField 2 g')
    (hc : ((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype y :
        GL (Fin m ⊕ Fin m) (GaloisField 2 g')) =
      1 + c • (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁))) :
    ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (iota y) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      altSiegelGroup (bmSDS_J n f) (ext a₁) (ext a₂) := by
  rw [altSiegelGroup]
  refine Subgroup.subset_closure ⟨r c, ?_⟩
  rw [bmSDS_transport_altSiegel_gen n f m g' r iota ext S e h y a₁ a₂ c hc]

private lemma bmSDS_altSiegel_mem_closure
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (X : Subgroup (ggU .PSp m g').K)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 g')) a₁ a₂)
    (g : (ggU .PSp m g').K) (hg : g ∈ X) :
    ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (iota g) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      altSiegelGroup (bmSDS_J n f) (ext a₁) (ext a₂) := by
  rw [bmSDS_altSiegel_X_eq_closure' m g' X a₁ a₂ hX] at hg
  refine Subgroup.closure_induction (p := fun y _ =>
      ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (iota y) :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
        altSiegelGroup (bmSDS_J n f) (ext a₁) (ext a₂)) ?_ ?_ ?_ ?_ hg
  · intro y hy
    obtain ⟨c, hc⟩ := Set.mem_preimage.mp hy
    exact bmSDS_altSiegel_gen_mem n f m g' r iota ext S e h y a₁ a₂ c hc
  · rw [map_one, map_one]; exact one_mem _
  · intro a b ha hb ha' hb'
    rw [map_mul, map_mul]; exact mul_mem ha' hb'
  · intro a ha ha'
    rw [map_inv, map_inv]; exact inv_mem ha'

private lemma bmSDS_altSiegel_map_le
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (X : Subgroup (ggU .PSp m g').K)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 g')) a₁ a₂) :
    X.map (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype).comp iota) ≤
      altSiegelGroup (bmSDS_J n f) (ext a₁) (ext a₂) := by
  rw [Subgroup.map_le_iff_le_comap]
  intro g hg
  exact bmSDS_altSiegel_mem_closure n f m g' r iota ext S e h X a₁ a₂ hX g hg

private lemma bmSDS_altSiegel_M_sq (m g' : ℕ)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g') :
    (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)) *
      (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)) =
      ((Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) ⬝ᵥ a₁) •
        (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)) := by
  have hJt : (Matrix.J (Fin m) (GaloisField 2 g')).transpose =
      Matrix.J (Fin m) (GaloisField 2 g') := by
    ext i j
    rcases i with a | a <;> rcases j with b | b <;>
      simp [Matrix.J, Matrix.one_apply, CharTwo.neg_eq, eq_comm]
  have h11 : (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁) ⬝ᵥ a₁ = 0 := by
    rw [dotProduct_comm, ← Matrix.toBilin'_apply', ← bmSDS_fromBlocks_eq_J]
    exact (bmSDS_B_isAlt m g').self_eq_zero a₁
  have h22 : (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) ⬝ᵥ a₂ = 0 := by
    rw [dotProduct_comm, ← Matrix.toBilin'_apply', ← bmSDS_fromBlocks_eq_J]
    exact (bmSDS_B_isAlt m g').self_eq_zero a₂
  have h12 : (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) ⬝ᵥ a₁ =
      (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁) ⬝ᵥ a₂ := by
    calc (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) ⬝ᵥ a₁
        = a₁ ⬝ᵥ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) :=
          dotProduct_comm _ _
      _ = a₂ ⬝ᵥ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')).transpose a₁) :=
        Matrix.dotProduct_transpose_mulVec
          (Matrix.J (Fin m) (GaloisField 2 g')).transpose a₁ a₂
      _ = a₂ ⬝ᵥ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁) := by rw [hJt]
      _ = (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁) ⬝ᵥ a₂ := dotProduct_comm _ _
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    h11, h22, h12, zero_smul]
  simp [smul_add, add_smul, smul_smul, add_assoc, add_comm, add_left_comm]

private lemma bmSDS_altSiegel_scalar_id (g' : ℕ) (c s : GaloisField 2 g')
    (hs : 1 + c * s ≠ 0) :
    c + c * (1 + c * s)⁻¹ + c * (1 + c * s)⁻¹ * (c * s) = 0 := by
  have hone : (1 : GaloisField 2 g') + 1 = 0 := by
    rw [← two_mul, CharTwo.two_eq_zero (R := GaloisField 2 g'), zero_mul]
  have h2 : c + c = 0 := by
    calc c + c = 2 * c := (two_mul c).symm
      _ = 0 * c := by rw [CharTwo.two_eq_zero (R := GaloisField 2 g')]
      _ = 0 := zero_mul c
  have h1 : c * (1 + c * s)⁻¹ * (1 + c * s) = c := by
    rw [mul_assoc, inv_mul_cancel₀ hs, mul_one]
  have hcs : c * s = (1 + c * s) + 1 := by
    rw [add_assoc, add_comm (c * s) 1, ← add_assoc, hone, zero_add]
  have h3 : c * (1 + c * s)⁻¹ * (c * s) = c + c * (1 + c * s)⁻¹ := by
    nth_rewrite 2 [hcs]
    rw [mul_add, mul_one, h1]
  have hx : (c + c * (1 + c * s)⁻¹) + (c + c * (1 + c * s)⁻¹) = 0 := by
    calc (c + c * (1 + c * s)⁻¹) + (c + c * (1 + c * s)⁻¹)
        = 2 * (c + c * (1 + c * s)⁻¹) := (two_mul _).symm
      _ = 0 * (c + c * (1 + c * s)⁻¹) := by rw [CharTwo.two_eq_zero (R := GaloisField 2 g')]
      _ = 0 := zero_mul _
  rw [h3]
  exact hx

private lemma bmSDS_altSiegel_M_mul_expand (m g' : ℕ)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g') (c : GaloisField 2 g') :
    (1 + c • (Matrix.vecMulVec a₁
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁))) *
      (1 + (c * (1 + c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁))⁻¹) •
        (Matrix.vecMulVec a₁
            (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁))) =
      1 + (c + c * (1 + c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁))⁻¹ +
          c * (1 + c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁))⁻¹ *
            (c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁))) •
        (Matrix.vecMulVec a₁
            (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)) := by
  let M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g') :=
    Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
      Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)
  let s : GaloisField 2 g' := (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁)
  have hM : M * M = s • M := bmSDS_altSiegel_M_sq m g' a₁ a₂
  change (1 + c • M) * (1 + (c * (1 + c * s)⁻¹) • M) =
    1 + (c + c * (1 + c * s)⁻¹ + c * (1 + c * s)⁻¹ * (c * s)) • M
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, hM, Matrix.one_mul]
  rw [add_assoc, add_assoc, ← add_smul, ← add_smul, ← add_assoc, ← add_assoc]
  congr 1
  ring_nf

private lemma bmSDS_altSiegel_M_mul (m g' : ℕ)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g') (c : GaloisField 2 g')
    (hs : 1 + c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁)
      ≠ 0) :
    (1 + c • (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁))) *
      (1 + (c * (1 + c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁))⁻¹) •
        (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁))) = 1 := by
  rw [bmSDS_altSiegel_M_mul_expand m g' a₁ a₂ c,
    bmSDS_altSiegel_scalar_id g' c
      (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁) hs, zero_smul,
    add_zero]

private lemma bmSDS_altSiegel_hcs (m g' : ℕ)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g') (c : GaloisField 2 g')
    (h : 1 + c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁) = 0) :
    c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁) = 1 := by
  have h' : (1 : GaloisField 2 g') =
      -(c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁)) :=
    eq_neg_of_add_eq_zero_left h
  rw [CharTwo.neg_eq] at h'
  exact h'.symm

private lemma bmSDS_altSiegel_M_a1 (m g' : ℕ)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g') :
    Matrix.mulVec
        (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)) a₁ =
      (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁) • a₁ := by
  rw [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  have h0 : (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁) ⬝ᵥ a₁ = 0 := by
    rw [dotProduct_comm, ← Matrix.toBilin'_apply', ← bmSDS_fromBlocks_eq_J]
    exact (bmSDS_B_isAlt m g').self_eq_zero a₁
  rw [h0]
  simp only [IsCentralScalar.op_smul_eq_smul, zero_smul, add_zero]

private lemma bmSDS_altSiegel_kernel (m g' : ℕ)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g') (c : GaloisField 2 g')
    (hcs : c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁) = 1) :
    Matrix.mulVec
        (1 + c • (Matrix.vecMulVec a₁
            (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁))) a₁ =
      0 := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    bmSDS_altSiegel_M_a1, smul_smul, hcs, one_smul]
  rw [← one_smul (GaloisField 2 g') a₁, ← one_smul (GaloisField 2 g') a₁, ← add_smul,
    show (1 : GaloisField 2 g') + 1 = 0 from CharTwo.add_self_eq_zero 1, zero_smul]

private lemma bmSDS_altSiegel_not_unit (m g' : ℕ)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g') (c : GaloisField 2 g')
    (h : 1 + c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁) = 0) :
    ¬ ∃ y : GL (Fin m ⊕ Fin m) (GaloisField 2 g'),
      (y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) = 1 + c •
        (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)) := by
  rintro ⟨y, hy⟩
  have hcs : c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁) = 1 :=
    bmSDS_altSiegel_hcs m g' a₁ a₂ c h
  have hker := bmSDS_altSiegel_kernel m g' a₁ a₂ c hcs
  have hya : (y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) *ᵥ a₁ = 0 := by
    rw [hy]; exact hker
  have hzero : a₁ = 0 := by
    have hconj := congrArg (fun v => ((y⁻¹ : GL (Fin m ⊕ Fin m) (GaloisField 2 g')) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) *ᵥ v) hya
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec] at hconj
    exact hconj
  have ha1 : a₁ ≠ 0 := by
    intro h0
    have hs0 : Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁ = 0 := by
      simp [h0]
    rw [hs0, mul_zero] at hcs
    exact one_ne_zero hcs.symm
  exact ha1 hzero

private lemma bmSDS_altSiegel_source_gen (m g' : ℕ)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g') (c : GaloisField 2 g')
    (hs : 1 + c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁)
      ≠ 0) :
    ∃ y₀ : GL (Fin m ⊕ Fin m) (GaloisField 2 g'),
      (y₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
        1 + c • (Matrix.vecMulVec a₁
            (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
          Matrix.vecMulVec a₂
            (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)) := by
  refine ⟨(IsUnit.of_mul_eq_one
    (1 + (c * (1 + c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁))⁻¹) •
      (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)))
    (bmSDS_altSiegel_M_mul m g' a₁ a₂ c hs)).unit, ?_⟩
  rw [IsUnit.unit_spec]

private lemma bmSDS_altSiegel_ge_hs (n f : ℕ)
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f) (d : GaloisField 2 f)
    (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hy : (y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + d • (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSDS_J n f) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (bmSDS_J n f) a₁))) :
    1 + d * (Matrix.mulVec (bmSDS_J n f) a₂ ⬝ᵥ a₁) ≠ 0 := by
  intro h
  refine bmSDS_altSiegel_not_unit n f a₁ a₂ d ?_ ⟨y, ?_⟩
  · rwa [show bmSDS_J n f = Matrix.J (Fin n) (GaloisField 2 f) from
        bmSDS_fromBlocks_eq_J n f] at h
  · rw [hy, show bmSDS_J n f = Matrix.J (Fin n) (GaloisField 2 f) from
        bmSDS_fromBlocks_eq_J n f]

private lemma bmSDS_altSiegel_ge_gen
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (X : Subgroup (ggU .PSp m g').K)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 g')) a₁ a₂)
    (d : GaloisField 2 f) (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hy : (y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + d • (Matrix.vecMulVec (ext a₁) (Matrix.mulVec (bmSDS_J n f) (ext a₂)) +
        Matrix.vecMulVec (ext a₂) (Matrix.mulVec (bmSDS_J n f) (ext a₁)))) :
    y ∈ X.map (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype).comp iota) := by
  obtain ⟨c, rfl⟩ := r.surjective d
  have hs' := bmSDS_altSiegel_ge_hs n f (ext a₁) (ext a₂) (r c) y hy
  have hs : 1 + c * (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂ ⬝ᵥ a₁) ≠ 0 := by
    intro h0
    apply hs'
    rw [← bmSDS_transv_gen_W_key n f m g' r ext S e iota h a₂ a₁]
    rw [← map_one r, ← map_mul, ← map_add, h0, map_zero]
  obtain ⟨y₀, hy₀⟩ := bmSDS_altSiegel_source_gen m g' a₁ a₂ c hs
  have hy₀mem : y₀ ∈ X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype := by
    rw [hX]
    exact Subgroup.subset_closure ⟨c, hy₀⟩
  obtain ⟨g, hgX, hgy₀⟩ : ∃ g ∈ X,
      (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype g = y₀ := hy₀mem
  have hc : (((CFSG.Open.StatedSp m (GaloisField 2 g')).subtype g :
      GL (Fin m ⊕ Fin m) (GaloisField 2 g')) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) =
      1 + c • (Matrix.vecMulVec a₁
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) a₁)) := by
    rw [hgy₀]
    exact hy₀
  refine Subgroup.mem_map.mpr ⟨g, hgX, ?_⟩
  apply Units.ext
  rw [MonoidHom.comp_apply,
    bmSDS_transport_altSiegel_gen n f m g' r iota ext S e h g a₁ a₂ c hc, hy]

private lemma bmSDS_altSiegel_ge
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (X : Subgroup (ggU .PSp m g').K)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 g')) a₁ a₂) :
    altSiegelGroup (bmSDS_J n f) (ext a₁) (ext a₂) ≤
      X.map (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype).comp iota) := by
  rw [altSiegelGroup, Subgroup.closure_le]
  rintro y ⟨d, hd⟩
  exact bmSDS_altSiegel_ge_gen n f m g' r iota ext S e h X a₁ a₂ hX d y hd

private lemma bmSDS_transport_altSiegel
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (iota : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') →
      ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r iota ext)
    (X : Subgroup (ggU .PSp m g').K)
    (a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hX : X.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype =
      altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 g')) a₁ a₂) :
    (X.map iota).map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      altSiegelGroup (bmSDS_J n f) (ext a₁) (ext a₂) := by
  rw [Subgroup.map_map]
  exact le_antisymm
    (bmSDS_altSiegel_map_le n f m g' r iota ext S e h X a₁ a₂ hX)
    (bmSDS_altSiegel_ge n f m g' r iota ext S e h X a₁ a₂ hX)

private lemma bmSDS_dim_rank_one
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hcard : Nat.card (GaloisField 2 f) = 2)
    (ι : CFSG.Open.StatedSp 1 (GaloisField 2 f) →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hιinj : Function.Injective ι) (hιrange : ι.range = bmSDS_Ge S e)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆) : False := by
  haveI hsGL : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 f)) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable _
      (Or.inl hcard)
  haveI hsSL : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →*
          Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 f)))
      Matrix.SpecialLinearGroup.toGL_injective
  haveI hsSp : Group.IsSolvable (CFSG.Open.StatedSp 1 (GaloisField 2 f)) :=
    Group.isSolvable_of_surjective
      (f := (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne
        (GaloisField 2 f)).toMonoidHom)
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne
        (GaloisField 2 f)).surjective
  haveI hsGe : Group.IsSolvable ↥(bmSDS_Ge S e) :=
    Group.isSolvable_of_surjective
      (f := ((MonoidHom.ofInjective hιinj).trans
        (MulEquiv.subgroupCongr hιrange)).toMonoidHom)
      ((MonoidHom.ofInjective hιinj).trans (MulEquiv.subgroupCongr hιrange)).surjective
  have hJ'le : J' ≤ bmSDS_Ge S e := hJe.1.trans (Subgroup.commutator_le_self _)
  haveI hsJ : Group.IsSolvable ↥J' :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hJ'le) (Subgroup.inclusion_injective hJ'le)
  haveI hSJ : IsSimpleGroup (↥J' ⧸ Subgroup.center ↥J') := hJe.2.2.2
  haveI hnt : Nontrivial ↥J' :=
    Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥J'))
  haveI hperf : Group.IsPerfect ↥J' := ⟨hJe.2.2.1⟩
  exact Group.IsPerfect.not_isSolvable ↥J' inferInstance

private lemma bmSDS_dim_rank_two
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hcard : Nat.card (GaloisField 2 f) = 2)
    (ι : CFSG.Open.StatedSp 2 (GaloisField 2 f) →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hιinj : Function.Injective ι) (hιrange : ι.range = bmSDS_Ge S e)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) : False := by
  let eGe : CFSG.Open.StatedSp 2 (GaloisField 2 f) ≃* ↥(bmSDS_Ge S e) :=
    (MonoidHom.ofInjective hιinj).trans (MulEquiv.subgroupCongr hιrange)
  have hmap : (commutator ↥(bmSDS_Ge S e)).map eGe.symm.toMonoidHom =
      commutator (CFSG.Open.StatedSp 2 (GaloisField 2 f)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 eGe.symm.surjective]
  let eC : ↥(commutator ↥(bmSDS_Ge S e)) ≃*
      ↥(commutator (CFSG.Open.StatedSp 2 (GaloisField 2 f))) :=
    ((commutator ↥(bmSDS_Ge S e)).equivMapOfInjective eGe.symm.toMonoidHom
        eGe.symm.injective).trans (MulEquiv.subgroupCongr hmap)
  have hmapGe : ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆ =
      (commutator ↥(bmSDS_Ge S e)).map (bmSDS_Ge S e).subtype := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  let e1 : ↥((commutator ↥(bmSDS_Ge S e)).map (bmSDS_Ge S e).subtype) ≃*
      ↥(commutator ↥(bmSDS_Ge S e)) :=
    (Subgroup.equivMapOfInjective (commutator ↥(bmSDS_Ge S e))
      (bmSDS_Ge S e).subtype (Subgroup.subtype_injective (bmSDS_Ge S e))).symm
  let eA : ↥⁅bmSDS_Ge S e, bmSDS_Ge S e⁆ ≃* ↥(alternatingGroup (Fin 6)) :=
    (MulEquiv.subgroupCongr hmapGe).trans (e1.trans (eC.trans
      (CFSG.Adapters.CatalogueFieldBridges.nonempty_commutator_statedSp_two_mulEquiv_alternating_six
        hcard).some))
  haveI hA6s : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hSimple : IsSimpleGroup ↥⁅bmSDS_Ge S e, bmSDS_Ge S e⁆ :=
    MulEquiv.isSimpleGroup eA
  have hJbot : J' = ⊥ ∨ J' = ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆ :=
    hJe.2.1.eq_bot_or_eq_of_isSimpleGroup hSimple
  have hne : J' ≠ ⊥ := by
    intro hbot
    haveI hSJ' : IsSimpleGroup (↥J' ⧸ Subgroup.center ↥J') := hJe.2.2.2
    haveI hnt : Nontrivial ↥J' :=
      Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥J'))
    rw [hbot] at hnt
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  rcases hJbot with h | h
  · exact hne h
  · exact hA6.false ((MulEquiv.subgroupCongr h).trans eA)

private lemma bmSDS_frozen1_dim_rank
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2)
    (hf : f ≤ 1)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    ∃ m : ℕ, Module.finrank (GaloisField 2 f) (bmSDS_W e) = m + m ∧ 3 ≤ m := by
  obtain ⟨m, ι, hιinj, hιrange, -, hfin, -, -, -⟩ :=
    bmSDS_blockGroup_iso_ext n f S hS he hadj hdeg
  refine ⟨m, hfin, ?_⟩
  have h2 : 2 ≤ Module.finrank (GaloisField 2 f) (bmSDS_W e) := by
    rw [← bmSDS_orthogonal_W' (n := n) (f := f) he.2.1 hadj]
    exact bmSDS_blockGroup_dim_two n f S he hadj
  have hm1 : 1 ≤ m := by omega
  by_contra hcon
  push Not at hcon
  have hcard : Nat.card (GaloisField 2 f) = 2 := bmSDS_blockGroup_card_small f hf
  interval_cases m
  · exact bmSDS_dim_rank_one n f S hcard ι hιinj hιrange hJe
  · exact bmSDS_dim_rank_two n f S hcard ι hιinj hιrange hJe hA6

private lemma bmSDS_frozen1_hK
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    4 ≤ Nat.card (GaloisField 2 f) ∨
      (Nat.card (GaloisField 2 f) = 3 ∧
        4 ≤ Module.finrank (GaloisField 2 f) ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e)))) ∨
      (Nat.card (GaloisField 2 f) = 2 ∧
        6 ≤ Module.finrank (GaloisField 2 f) ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e)))) := by
  by_cases hf : f ≤ 1
  · refine Or.inr (Or.inr ⟨bmSDS_blockGroup_card_small f hf, ?_⟩)
    rw [bmSDS_orthogonal_W' (n := n) (f := f) he.2.1 hadj]
    obtain ⟨m, hm, h3⟩ := bmSDS_frozen1_dim_rank n f S hS he hadj hdeg hf hJe hA6
    omega
  · exact Or.inl (bmSDS_blockGroup_card_large f (by omega))

private lemma bmSDS_component_eq_no_small
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2)
    (h2 : 2 ≤ Module.finrank (GaloisField 2 f)
        ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e))))
    (hK : 4 ≤ Nat.card (GaloisField 2 f) ∨
      (Nat.card (GaloisField 2 f) = 3 ∧
        4 ≤ Module.finrank (GaloisField 2 f)
          ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e)))) ∨
      (Nat.card (GaloisField 2 f) = 2 ∧
        6 ≤ Module.finrank (GaloisField 2 f)
          ((bmSDS_B n f).orthogonal (bmSDS_W (1 - e)))))
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆) :
    J' = bmSDS_Ge S e := by
  exact bmSDS_component_eq_top n f S hJe
    (bmSDS_blockGroup_component n f S
      (bmSDS_blockGroup_quasisimple n f S hS he hadj hdeg h2 hK)
      (bmSDS_blockGroup_perfect n f S hS he hadj hdeg h2 hK))

private lemma bmSDS_hT_gen
    (n f m g' : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r ι ext) :
    ∀ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g'),
      (((ggU .PSp m g').D.rootGroup β₀).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup v₀
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) →
      ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f,
        (((ggU .PSp m g').D.rootGroup β₀).map ι).map
            ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) := by
  intro β₀ v₀ hv
  exact ⟨ext v₀, bmSDS_transport_rootGroup n f m g' r ι ext S e h
    ((ggU .PSp m g').D.rootGroup β₀) v₀ hv⟩

private lemma bmSDS_longRoot_mem_roots
    (m g' : ℕ)
    (γ : Fin (ggU .PSp m g').D.rank → ℤ)
    (h : GGLongRoot (ggU .PSp m g').D γ) :
    γ ∈ (ggU .PSp m g').D.roots := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := h
  exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w

private lemma bmSDS_PSp_conj_one_map
    (m g' : ℕ) (H : Subgroup (CFSG.Open.StatedSp m (GaloisField 2 g'))) :
    Subgroup.map
        (MulEquiv.toMonoidHom (MulAut.conj (1 : CFSG.Open.StatedSp m (GaloisField 2 g')))) H =
      H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x, hx, by simp⟩

private lemma bmSDS_PSp_spPair_raw
    (m g' : ℕ)
    (γ : Fin (Symplectic.rootDatum m (GaloisField 2 g')).rank → ℤ)
    (hβ : γ ∈ (Symplectic.rootDatum m (GaloisField 2 g')).roots)
    (hlong : GGLongRoot (Symplectic.rootDatum m (GaloisField 2 g')) γ) :
    ∃ v₀ w₀ : (Fin m ⊕ Fin m) → GaloisField 2 g',
      v₀ ⬝ᵥ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) w₀) = 1 ∧
      (Subgroup.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype
        ((Symplectic.rootDatum m (GaloisField 2 g')).rootGroup γ)) =
        matTransvGroup v₀ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) v₀) ∧
      (Subgroup.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype
        ((Symplectic.rootDatum m (GaloisField 2 g')).rootGroup (-γ))) =
        matTransvGroup w₀ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) w₀) := by
  obtain ⟨v₀, w₀, hpair, hv, hw⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_matTransvGroup_eq_conj_rootGroup_Sp
      m (GaloisField 2 g') hβ hlong 1
  refine ⟨v₀, w₀, hpair, ?_, ?_⟩
  · rw [bmSDS_PSp_conj_one_map m g'] at hv
    exact hv
  · rw [bmSDS_PSp_conj_one_map m g'] at hw
    exact hw

private lemma bmSDS_spRootTransv_pair
    (m g' : ℕ)
    (γ : Fin (ggU .PSp m g').D.rank → ℤ)
    (hβ : γ ∈ (ggU .PSp m g').D.roots)
    (hlong : GGLongRoot (ggU .PSp m g').D γ) :
    ∃ v₀ w₀ : (Fin m ⊕ Fin m) → GaloisField 2 g',
      v₀ ⬝ᵥ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) w₀) = 1 ∧
      (Subgroup.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype
        ((ggU .PSp m g').D.rootGroup γ)) =
        matTransvGroup v₀ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) v₀) ∧
      (Subgroup.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype
        ((ggU .PSp m g').D.rootGroup (-γ))) =
        matTransvGroup w₀ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) w₀) := by
  obtain ⟨v₀, w₀, hpair, hv, hw⟩ := bmSDS_PSp_spPair_raw m g' γ hβ hlong
  exact ⟨v₀, w₀, hpair, hv, hw⟩

private lemma bmSDS_hneg_model_pair (m g' : ℕ)
    (β₀ : Fin (ggU .PSp m g').D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSp m g').D β₀) :
    ∃ v₀ w₀ : (Fin m ⊕ Fin m) → GaloisField 2 g',
      v₀ ⬝ᵥ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) w₀) = 1 ∧
      (((ggU .PSp m g').D.rootGroup β₀).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) ∧
      (((ggU .PSp m g').D.rootGroup (-β₀)).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup w₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) w₀) := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hlong
  have hβ := bmSDS_longRoot_mem_roots m g'
    (weylAction (ggU .PSp m g').D.isFiniteType w γ₀) ⟨w, γ₀, hγ₀, hmax, rfl⟩
  obtain ⟨v₀, w₀, hpair, hv, hw⟩ := bmSDS_spRootTransv_pair m g'
    (weylAction (ggU .PSp m g').D.isFiniteType w γ₀) hβ ⟨w, γ₀, hγ₀, hmax, rfl⟩
  rw [bmSDS_fromBlocks_eq_J m g'] at hpair hv hw
  exact ⟨v₀, w₀, hpair, hv, hw⟩

private lemma bmSDS_spGram_eq (n f : ℕ) :
    CFSG.Timmesfeld.ARS.CaseM.spGram n (GaloisField 2 f) = bmSDS_J n f := by
  rfl

private lemma bmSDS_transvGen_sq_zero (n f : ℕ)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v) *
        Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v) = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have h0 : (Matrix.mulVec (bmSDS_J n f) v) ⬝ᵥ v = 0 := by
    rw [dotProduct_comm, ← Matrix.toBilin'_apply']
    exact (bmSDS_B_isAlt n f).self_eq_zero v
  rw [h0, zero_smul, Matrix.vecMulVec_zero]

private lemma bmSDS_transvGen_mul (n f : ℕ)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (c c' : GaloisField 2 f) :
    (1 + c • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v)) *
        (1 + c' • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v)) =
      1 + (c + c') • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, bmSDS_transvGen_sq_zero n f v,
    smul_zero, add_zero]
  rw [add_assoc, ← add_smul, add_comm]

private lemma bmSDS_transvGen_mul_self (n f : ℕ)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (c : GaloisField 2 f) :
    (1 + c • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v)) *
        (1 + c • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v)) = 1 := by
  rw [bmSDS_transvGen_mul n f v c c]
  have hcc : c + c = 0 := by
    rw [← two_nsmul, nsmul_eq_mul, CharP.cast_eq_zero (GaloisField 2 f) 2, zero_mul]
  rw [hcc, zero_smul, add_zero]

private lemma bmSDS_transvGen_inv_mem (n f : ℕ)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (x : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hx : ∃ c : GaloisField 2 f,
      (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        1 + c • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v)) :
    ∃ c : GaloisField 2 f,
      ((x⁻¹ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        1 + c • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v) := by
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, ?_⟩
  have hxx : x * x = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simpa only [Units.val_mul, Units.val_one, hc] using
      congrFun (congrFun (bmSDS_transvGen_mul_self n f v c) i) j
  rw [inv_eq_of_mul_eq_one_right hxx]
  exact hc

private lemma bmSDS_transvGen_closure_subset (n f : ℕ)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (x : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hx : x ∈ matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v)) :
    ∃ c : GaloisField 2 f,
      (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        1 + c • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one => exact ⟨0, by simp⟩
  | mul y z _ _ ihy ihz =>
      obtain ⟨c, hc⟩ := ihy
      obtain ⟨d, hd⟩ := ihz
      exact ⟨c + d, by rw [Units.val_mul, hc, hd, bmSDS_transvGen_mul n f v c d]⟩
  | inv y _ ihy => exact bmSDS_transvGen_inv_mem n f v y ihy

private lemma bmSDS_matTransvGroup_mem_iff (n f : ℕ)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (x : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
    x ∈ matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) ↔
      ∃ c : GaloisField 2 f,
        (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
          1 + c • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v) := by
  constructor
  · exact bmSDS_transvGen_closure_subset n f v x
  · intro hx
    exact Subgroup.subset_closure hx

private lemma bmSDS_caseM_spTrans_eq (n f : ℕ)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f) (c : GaloisField 2 f) :
    CFSG.Timmesfeld.ARS.CaseM.spTrans v c =
      1 + c • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v) := by
  rw [CFSG.Timmesfeld.ARS.CaseM.spTrans, CFSG.Timmesfeld.ARS.CaseM.spNil, bmSDS_spGram_eq]
  congr 2
  rw [← Matrix.mulVec_transpose (bmSDS_J n f) v,
    show (bmSDS_J n f).transpose = bmSDS_J n f from by
      ext a b
      rcases a with a | a <;> rcases b with b | b <;>
        simp [bmSDS_J, Matrix.one_apply, CharTwo.neg_eq, eq_comm]]

private lemma bmSDS_caseM_spTrans_mem (n f : ℕ)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f) (c : GaloisField 2 f) :
    ∃ x : CFSG.Open.StatedSp n (GaloisField 2 f),
      (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        CFSG.Timmesfeld.ARS.CaseM.spTrans v c := by
  obtain ⟨x, hx⟩ := CFSG.Timmesfeld.Transvection.ModelRank.exists_mat_eq_spTrans
    (n := n) (K := GaloisField 2 f) v c
  exact ⟨x, by
    show CFSG.LieType.Universal.Symplectic.SpExtras.mat n (GaloisField 2 f) x =
      CFSG.Timmesfeld.ARS.CaseM.spTrans v c
    exact hx⟩

private lemma bmSDS_isTransGroup_matTransvGroup (n f : ℕ)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    CFSG.Timmesfeld.ARS.CaseM.IsTransGroup v
      (Subgroup.comap (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        (matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v))) := by
  refine ⟨fun x => ?_, fun c => bmSDS_caseM_spTrans_mem n f v c⟩
  constructor
  · intro hx
    have hx' : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x ∈
        matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) := hx
    obtain ⟨c, hc⟩ := (bmSDS_matTransvGroup_mem_iff n f v
      ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x)).mp hx'
    exact ⟨c, by
      show (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        CFSG.Timmesfeld.ARS.CaseM.spTrans v c
      rw [hc, bmSDS_caseM_spTrans_eq n f v c]⟩
  · rintro ⟨c, hc⟩
    show (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x ∈
      matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v)
    refine (bmSDS_matTransvGroup_mem_iff n f v
      ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x)).mpr ⟨c, ?_⟩
    show CFSG.LieType.Universal.Symplectic.SpExtras.mat n (GaloisField 2 f) x =
      1 + c • Matrix.vecMulVec v (Matrix.mulVec (bmSDS_J n f) v)
    rw [hc, bmSDS_caseM_spTrans_eq n f v c]

private lemma bmSDS_matTransvGroup_eq_smul (n f : ℕ)
    (v w : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (h : matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) =
      matTransvGroup w (Matrix.mulVec (bmSDS_J n f) w)) :
    ∃ μ : GaloisField 2 f, μ ≠ 0 ∧ v = μ • w := by
  by_cases hv0 : v = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    have hw0 : w = 0 := by
      by_contra hw
      have hX := bmSDS_isTransGroup_matTransvGroup n f w
      have hX' : CFSG.Timmesfeld.ARS.CaseM.IsTransGroup v
          (Subgroup.comap (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
            (matTransvGroup w (Matrix.mulVec (bmSDS_J n f) w))) := by
        rw [← h]
        exact bmSDS_isTransGroup_matTransvGroup n f v
      obtain ⟨μ, _, hwv⟩ :=
        CFSG.Timmesfeld.Transvection.ModelRank.IsTransGroup.exists_eq_smul hX hX' hw
      exact hw (by rw [hwv, hv0, smul_zero])
    rw [hv0, hw0, one_smul]
  · have hX := bmSDS_isTransGroup_matTransvGroup n f v
    have hX' : CFSG.Timmesfeld.ARS.CaseM.IsTransGroup w
        (Subgroup.comap (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
          (matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v))) := by
      rw [h]
      exact bmSDS_isTransGroup_matTransvGroup n f w
    exact CFSG.Timmesfeld.Transvection.ModelRank.IsTransGroup.exists_eq_smul hX hX' hv0

private lemma bmSDS_hneg_vec_eq (m g' n f : ℕ)
    (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (hv' : matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) =
      matTransvGroup (ext v₀) (Matrix.mulVec (bmSDS_J n f) (ext v₀))) :
    ∃ μ : GaloisField 2 f, μ ≠ 0 ∧ v = μ • ext v₀ := by
  obtain ⟨μ, hμ, hvμ⟩ := bmSDS_matTransvGroup_eq_smul n f v (ext v₀) hv'
  exact ⟨μ, hμ, hvμ⟩

private lemma bmSDS_matTransvGroup_smul_left (n f : ℕ)
    (a : GaloisField 2 f) (ha : a ≠ 0)
    (v φ : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    matTransvGroup (a • v) φ = matTransvGroup v φ := by
  unfold matTransvGroup
  congr 1
  ext g
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c * a, ?_⟩
    rw [hc, Matrix.smul_vecMulVec, smul_smul]
  · rintro ⟨c, hc⟩
    refine ⟨c * a⁻¹, ?_⟩
    rw [hc, Matrix.smul_vecMulVec, smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]

private lemma bmSDS_matTransvGroup_smul_right (n f : ℕ)
    (a : GaloisField 2 f) (ha : a ≠ 0)
    (v φ : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    matTransvGroup v (a • φ) = matTransvGroup v φ := by
  unfold matTransvGroup
  congr 1
  ext g
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c * a, ?_⟩
    rw [hc, Matrix.vecMulVec_smul, smul_smul]
  · rintro ⟨c, hc⟩
    refine ⟨c * a⁻¹, ?_⟩
    rw [hc, Matrix.vecMulVec_smul, smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]

private lemma bmSDS_hneg_pair_transport (n f m g' : ℕ)
    (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (v₀ w₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (hext : ∀ u u', bmSDS_B n f (ext u) (ext u') =
      r (u ⬝ᵥ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) u')))
    (hpair : v₀ ⬝ᵥ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) w₀) = 1)
    (hv : ∃ μ : GaloisField 2 f, μ ≠ 0 ∧ v = μ • ext v₀) :
    ∃ w : (Fin n ⊕ Fin n) → GaloisField 2 f,
      v ⬝ᵥ (Matrix.mulVec (bmSDS_J n f) w) = 1 ∧
      matTransvGroup (ext w₀) (Matrix.mulVec (bmSDS_J n f) (ext w₀)) =
        matTransvGroup w (Matrix.mulVec (bmSDS_J n f) w) := by
  obtain ⟨μ, hμ, hvμ⟩ := hv
  refine ⟨μ⁻¹ • ext w₀, ?_, ?_⟩
  · rw [hvμ, Matrix.mulVec_smul]
    have hB : (ext v₀) ⬝ᵥ Matrix.mulVec (bmSDS_J n f) (ext w₀) =
        bmSDS_B n f (ext v₀) (ext w₀) := by
      rw [bmSDS_B, Matrix.toBilin'_apply']
    rw [show (μ • ext v₀) ⬝ᵥ (μ⁻¹ • Matrix.mulVec (bmSDS_J n f) (ext w₀)) =
        μ • (μ⁻¹ • ((ext v₀) ⬝ᵥ Matrix.mulVec (bmSDS_J n f) (ext w₀))) from by
      rw [smul_dotProduct, dotProduct_smul]]
    rw [smul_smul, mul_inv_cancel₀ hμ, one_smul, hB, hext v₀ w₀, hpair, map_one]
  · rw [Matrix.mulVec_smul]
    exact ((bmSDS_matTransvGroup_smul_left n f μ⁻¹ (inv_ne_zero hμ) (ext w₀)
        (μ⁻¹ • Matrix.mulVec (bmSDS_J n f) (ext w₀))).trans
      (bmSDS_matTransvGroup_smul_right n f μ⁻¹ (inv_ne_zero hμ) (ext w₀)
        (Matrix.mulVec (bmSDS_J n f) (ext w₀)))).symm

private lemma bmSDS_hneg_opposite_transport
    (n f m g' : ℕ) (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (ι : (ggU .PSp m g').K →* CFSG.Open.StatedSp n (GaloisField 2 f))
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r ι ext)
    (β₀ : Fin (ggU .PSp m g').D.rank → ℤ)
    (w₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hw₀ : (((ggU .PSp m g').D.rootGroup (-β₀)).map
        (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
      matTransvGroup w₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) w₀)) :
    (((ggU .PSp m g').D.rootGroup (-β₀)).map ι).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
      matTransvGroup (ext w₀) (Matrix.mulVec (bmSDS_J n f) (ext w₀)) := by
  exact bmSDS_transport_rootGroup n f m g' r ι ext S e h
    ((ggU .PSp m g').D.rootGroup (-β₀)) w₀ hw₀

private lemma bmSDS_hneg_gen
    (n f m g' : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r ι ext) :
    ∀ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ), GGLongRoot (ggU .PSp m g').D β₀ →
      ∀ (v : (Fin n ⊕ Fin n) → GaloisField 2 f),
      (((ggU .PSp m g').D.rootGroup β₀).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) →
      ∃ w : (Fin n ⊕ Fin n) → GaloisField 2 f,
        v ⬝ᵥ (Matrix.mulVec (bmSDS_J n f) w) = 1 ∧
        (((ggU .PSp m g').D.rootGroup (-β₀)).map ι).map
            ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          matTransvGroup w (Matrix.mulVec (bmSDS_J n f) w) := by
  intro β₀ hlong v hv
  obtain ⟨v₀, w₀, hpair, hv₀, hw₀⟩ := bmSDS_hneg_model_pair m g' β₀ hlong
  have hv' : matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) =
      matTransvGroup (ext v₀) (Matrix.mulVec (bmSDS_J n f) (ext v₀)) := by
    rw [← hv, bmSDS_transport_rootGroup n f m g' r ι ext S e h
      ((ggU .PSp m g').D.rootGroup β₀) v₀ hv₀]
  obtain ⟨μ, hμ, hvμ⟩ := bmSDS_hneg_vec_eq m g' n f v₀ v ext hv'
  obtain ⟨w, hw1, hw2⟩ := bmSDS_hneg_pair_transport n f m g' r ext v₀ w₀ v
    h.2.2.2.2.2.2.1 hpair ⟨μ, hμ, hvμ⟩
  exact ⟨w, hw1,
    (bmSDS_hneg_opposite_transport n f m g' r ι ext S e h β₀ w₀ hw₀).trans hw2⟩

private lemma bmSDS_frozen1_root_pkg
    (n f m g' : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hrange : ι.range = bmSDS_Ge S e)
    (hT : (∀ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ) (v₀ : (Fin m ⊕ Fin m) → GaloisField 2 g'),
      (((ggU .PSp m g').D.rootGroup β₀).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup v₀
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) v₀) →
      ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f,
        (((ggU .PSp m g').D.rootGroup β₀).map ι).map
            ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v)))
    (hneg : (∀ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ), GGLongRoot (ggU .PSp m g').D β₀ →
      ∀ (v : (Fin n ⊕ Fin n) → GaloisField 2 f),
      (((ggU .PSp m g').D.rootGroup β₀).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) →
      ∃ w : (Fin n ⊕ Fin n) → GaloisField 2 f,
        v ⬝ᵥ (Matrix.mulVec (bmSDS_J n f) w) = 1 ∧
        (((ggU .PSp m g').D.rootGroup (-β₀)).map ι).map
            ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          matTransvGroup w (Matrix.mulVec (bmSDS_J n f) w))) :
        ∃ (β₀ : Fin (ggU .PSp m g').D.rank → ℤ)
      (v w : (Fin n ⊕ Fin n) → GaloisField 2 f),
      GGLongRoot (ggU .PSp m g').D β₀ ∧ v ⬝ᵥ (Matrix.mulVec (bmSDS_J n f) w) = 1 ∧
      (((ggU .PSp m g').D.rootGroup β₀).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup v (Matrix.mulVec (bmSDS_J n f) v) ∧
      (((ggU .PSp m g').D.rootGroup (-β₀)).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup w (Matrix.mulVec (bmSDS_J n f) w) :=
  bmSDS_root_transport n f m g' S hJe ι hrange hT hneg

private lemma bmSDS_closure_vec_mem
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6)))
    (v₀ : (Fin n ⊕ Fin n) → GaloisField 2 f) (hv₀ : v₀ ≠ 0)
    (hle : matTransvGroup v₀ (Matrix.mulVec (bmSDS_J n f) v₀) ≤
      J'.map ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)) :
    v₀ ∈ bmSDS_W e := by
  have hcomp : J' = bmSDS_Ge S e :=
    bmSDS_component_eq_no_small n f S hS he hadj hdeg
      (bmSDS_blockGroup_dim_two n f S he hadj)
      (bmSDS_frozen1_hK n f S hS he hadj hdeg hJe hA6) hJe
  have hle' : matTransvGroup v₀ (Matrix.mulVec (bmSDS_J n f) v₀) ≤
      (bmSDS_Ge S e).map ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) := by
    simpa only [hcomp] using hle
  have hGeFix : (bmSDS_Ge S e).map ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) ≤
      glFixing (1 - e) := by
    rintro y ⟨x, hx, rfl⟩
    exact (show ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x) ∈
      Subgroup.centralizer S ⊓ glFixing (1 - e) from hx).2
  rw [← bmSDS_orthogonal_W' (n := n) (f := f) he.2.1 hadj,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro w' hw'
  rw [bmSDS_W] at hw'
  obtain ⟨y, rfl⟩ := hw'
  rw [Matrix.mulVecLin_apply]
  obtain ⟨g, hg⟩ := bmSDS_transv_source_gen n f v₀ 1
  have hg' : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + Matrix.vecMulVec v₀ (Matrix.mulVec (bmSDS_J n f) v₀) := by
    simpa only [bmSDS_J, bmSDS_fromBlocks_eq_J, one_smul] using hg
  have hgT : g ∈ matTransvGroup v₀ (Matrix.mulVec (bmSDS_J n f) v₀) :=
    Subgroup.subset_closure ⟨1, by simpa using hg'⟩
  have hfix : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) = 1 - e :=
    hGeFix (hle' hgT)
  have hgw : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ
      ((1 - e) *ᵥ y) = (1 - e) *ᵥ y := by
    rw [Matrix.mulVec_mulVec, hfix]
  have hzero : ((Matrix.mulVec (bmSDS_J n f) v₀) ⬝ᵥ ((1 - e) *ᵥ y)) • v₀ = 0 := by
    have h := hgw
    rw [hg'] at h
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
      IsCentralScalar.op_smul_eq_smul] at h
    exact add_left_cancel (h.trans (add_zero _).symm)
  have hc : (Matrix.mulVec (bmSDS_J n f) v₀) ⬝ᵥ ((1 - e) *ᵥ y) = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hv₀
  rw [bmSDS_B, Matrix.toBilin'_apply', dotProduct_comm]
  exact hc

private lemma bmSDS_hyperbolic_partner (m g' : ℕ)
    (u₀ : (Fin m ⊕ Fin m) → GaloisField 2 g') (hu₀ : u₀ ≠ 0) :
    ∃ w₀ : (Fin m ⊕ Fin m) → GaloisField 2 g',
      u₀ ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') w₀) = 1 := by
  have hne : ¬ ∀ w₀, bmSDS_B m g' u₀ w₀ = 0 :=
    fun h => hu₀ ((bmSDS_B_nondegenerate m g').left u₀ h)
  push Not at hne
  obtain ⟨w, hw⟩ := hne
  have hbw : u₀ ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') w) = bmSDS_B m g' u₀ w := by
    rw [bmSDS_B, Matrix.toBilin'_apply']
  refine ⟨(bmSDS_B m g' u₀ w)⁻¹ • w, ?_⟩
  rw [Matrix.mulVec_smul, dotProduct_smul, hbw, smul_eq_mul, inv_mul_cancel₀ hw]

private lemma bmSDS_model_root_conj
    (m g' : ℕ) (hm : 1 ≤ m)
    (u₀ : (Fin m ⊕ Fin m) → GaloisField 2 g') (hu₀ : u₀ ≠ 0) :
    ∃ (β : Fin (ggU .PSp m g').D.rank → ℤ) (u : (ggU .PSp m g').K),
      β ∈ (ggU .PSp m g').D.roots ∧ GGLongRoot (ggU .PSp m g').D β ∧
      ((((ggU .PSp m g').D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        matTransvGroup u₀
          (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) u₀) := by
  obtain ⟨w₀, hw₀⟩ := bmSDS_hyperbolic_partner m g' u₀ hu₀
  obtain ⟨β, hβ, hlβ, u, hconj, -⟩ :=
    exists_conj_rootGroup_eq_matTransvGroup_PSp m (GaloisField 2 g') hm u₀ w₀ hw₀
  refine ⟨β, u, hβ, hlβ, ?_⟩
  have hconj' : (Subgroup.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype
      (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u))
        ((ggU .PSp m g').D.rootGroup β))) =
      matTransvGroup u₀ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) u₀) := hconj
  rw [bmSDS_fromBlocks_eq_J m g'] at hconj'
  exact hconj'

private lemma bmSDS_closure_transport
    (n f m g' : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r ι ext)
    (u₀ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (v₀ : (Fin n ⊕ Fin n) → GaloisField 2 f) (hv₀eq : ext u₀ = v₀)
    (u : (ggU .PSp m g').K)
    {β : Fin (ggU .PSp m g').D.rank → ℤ}
    (hconj : (Subgroup.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype
        (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u))
          ((ggU .PSp m g').D.rootGroup β))) =
      matTransvGroup u₀
        (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 g')) u₀)) :
    ((((ggU .PSp m g').D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
      matTransvGroup v₀ (Matrix.mulVec (bmSDS_J n f) v₀) := by
  have htr := bmSDS_transport_rootGroup n f m g' r ι ext S e h
    (((ggU .PSp m g').D.rootGroup β).map (MulAut.conj u).toMonoidHom) u₀ hconj
  rw [htr, hv₀eq]

private theorem bmSDS_closure_long
    (n f m g' : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6)))
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hrange : ι.range = bmSDS_Ge S e)
    (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r ι ext)
    (v₀ : (Fin n ⊕ Fin n) → GaloisField 2 f) (hv₀ : v₀ ≠ 0)
    (hle : matTransvGroup v₀ (Matrix.mulVec (bmSDS_J n f) v₀) ≤
      J'.map ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)) :
    ∃ (β : Fin (ggU .PSp m g').D.rank → ℤ) (u : (ggU .PSp m g').K),
      β ∈ (ggU .PSp m g').D.roots ∧ GGLongRoot (ggU .PSp m g').D β ∧
      ((((ggU .PSp m g').D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        matTransvGroup v₀ (Matrix.mulVec (bmSDS_J n f) v₀) := by
  have hm : 1 ≤ m := bmSDS_one_le_m hJe ι hrange
  have hvW : v₀ ∈ bmSDS_W e :=
    bmSDS_closure_vec_mem n f S hS he hadj hdeg hJe hA6 v₀ hv₀ hle
  obtain ⟨u₀, hu₀eq⟩ := (h.2.2.2.1 v₀).1 hvW
  have hu₀ : u₀ ≠ 0 := by
    intro h0
    apply hv₀
    have h0e : ext 0 = 0 := by
      simpa using h.2.2.2.2.2.1 (0 : GaloisField 2 g') (0 : (Fin m ⊕ Fin m) → GaloisField 2 g')
    rw [← hu₀eq, h0, h0e]
  obtain ⟨β, u, hβ, hlβ, hconj⟩ := bmSDS_model_root_conj m g' hm u₀ hu₀
  exact ⟨β, u, hβ, hlβ,
    bmSDS_closure_transport n f m g' S ι r ext h
      u₀ v₀ hu₀eq u hconj⟩

private lemma bmSDS_closure_siegel_plane_mem
    (n f m g' : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6)))
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r ι ext)
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (horth : a₁ ⬝ᵥ (Matrix.mulVec (bmSDS_J n f) a₂) = 0)
    (hle : altSiegelGroup (bmSDS_J n f) a₁ a₂ ≤
      J'.map ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)) :
    ∃ b₁ b₂ : (Fin m ⊕ Fin m) → GaloisField 2 g',
      ext b₁ = a₁ ∧ ext b₂ = a₂ ∧ b₁ ≠ 0 ∧ b₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 g') ![b₁, b₂] ∧
      b₁ ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') b₂) = 0 := by
  have hcomp : J' = bmSDS_Ge S e :=
    bmSDS_component_eq_no_small n f S hS he hadj hdeg
      (bmSDS_blockGroup_dim_two n f S he hadj)
      (bmSDS_frozen1_hK n f S hS he hadj hdeg hJe hA6) hJe
  have hle' : altSiegelGroup (bmSDS_J n f) a₁ a₂ ≤
      (bmSDS_Ge S e).map ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) := by
    simpa only [hcomp] using hle
  have hGeFix : (bmSDS_Ge S e).map ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) ≤
      glFixing (1 - e) := by
    rintro y ⟨x, hx, rfl⟩
    exact (show ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x) ∈
      Subgroup.centralizer S ⊓ glFixing (1 - e) from hx).2
  have hJ₁ : (Matrix.mulVec (Matrix.J (Fin n) (GaloisField 2 f)) a₂) ⬝ᵥ a₁ = 0 := by
    rw [dotProduct_comm, ← bmSDS_fromBlocks_eq_J n f]
    exact horth
  have hsJ : (1 : GaloisField 2 f) + (1 : GaloisField 2 f) *
      (Matrix.mulVec (Matrix.J (Fin n) (GaloisField 2 f)) a₂ ⬝ᵥ a₁) ≠ 0 := by
    rw [hJ₁, mul_zero, add_zero]
    exact one_ne_zero
  obtain ⟨g, hg⟩ := bmSDS_altSiegel_source_gen n f a₁ a₂ 1 hsJ
  have hg' : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSDS_J n f) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (bmSDS_J n f) a₁)) := by
    rw [hg]
    simp only [← bmSDS_fromBlocks_eq_J, one_smul]
  have hgT : g ∈ altSiegelGroup (bmSDS_J n f) a₁ a₂ :=
    Subgroup.subset_closure ⟨1, by simpa using hg'⟩
  have hfix : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) = 1 - e :=
    hGeFix (hle' hgT)
  have key : ∀ y : (Fin n ⊕ Fin n) → GaloisField 2 f,
      ((Matrix.mulVec (bmSDS_J n f) a₁) ⬝ᵥ ((1 - e) *ᵥ y)) = 0 ∧
      ((Matrix.mulVec (bmSDS_J n f) a₂) ⬝ᵥ ((1 - e) *ᵥ y)) = 0 := by
    intro y
    have hgw : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ
        ((1 - e) *ᵥ y) = (1 - e) *ᵥ y := by
      rw [Matrix.mulVec_mulVec, hfix]
    have hsum : ((Matrix.mulVec (bmSDS_J n f) a₂) ⬝ᵥ ((1 - e) *ᵥ y)) • a₁ +
        ((Matrix.mulVec (bmSDS_J n f) a₁) ⬝ᵥ ((1 - e) *ᵥ y)) • a₂ = 0 := by
      have h := hgw
      rw [hg'] at h
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
        Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
        IsCentralScalar.op_smul_eq_smul, IsCentralScalar.op_smul_eq_smul] at h
      exact add_left_cancel (h.trans (add_zero _).symm)
    obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp hli)
      ((Matrix.mulVec (bmSDS_J n f) a₂) ⬝ᵥ ((1 - e) *ᵥ y))
      ((Matrix.mulVec (bmSDS_J n f) a₁) ⬝ᵥ ((1 - e) *ᵥ y)) hsum
    exact ⟨h2, h1⟩
  have h0e : ext 0 = 0 := by
    simpa using h.2.2.2.2.2.1 (0 : GaloisField 2 g') (0 : (Fin m ⊕ Fin m) → GaloisField 2 g')
  have ha₁W : a₁ ∈ bmSDS_W e := by
    rw [← bmSDS_orthogonal_W' (n := n) (f := f) he.2.1 hadj,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro w' hw'
    rw [bmSDS_W] at hw'
    obtain ⟨y, rfl⟩ := hw'
    rw [Matrix.mulVecLin_apply, bmSDS_B, Matrix.toBilin'_apply', dotProduct_comm]
    exact (key y).1
  have ha₂W : a₂ ∈ bmSDS_W e := by
    rw [← bmSDS_orthogonal_W' (n := n) (f := f) he.2.1 hadj,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro w' hw'
    rw [bmSDS_W] at hw'
    obtain ⟨y, rfl⟩ := hw'
    rw [Matrix.mulVecLin_apply, bmSDS_B, Matrix.toBilin'_apply', dotProduct_comm]
    exact (key y).2
  obtain ⟨b₁, hb₁eq⟩ := (h.2.2.2.1 a₁).1 ha₁W
  obtain ⟨b₂, hb₂eq⟩ := (h.2.2.2.1 a₂).1 ha₂W
  have hb₁ : b₁ ≠ 0 := by
    intro h0
    apply ha₁
    rw [← hb₁eq, h0, h0e]
  have hb₂ : b₂ ≠ 0 := by
    intro h0
    apply ha₂
    rw [← hb₂eq, h0, h0e]
  have hbLi : LinearIndependent (GaloisField 2 g') ![b₁, b₂] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro s t hst
    have hh := congrArg ext hst
    rw [h0e] at hh
    rw [h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.1, hb₁eq, hb₂eq] at hh
    obtain ⟨hs, ht⟩ := hli (r s) (r t) hh
    exact ⟨r.injective (by simpa using hs), r.injective (by simpa using ht)⟩
  have hbOrth : b₁ ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') b₂) = 0 := by
    apply r.injective
    rw [map_zero, show bmSDS_J m g' = Matrix.J (Fin m) (GaloisField 2 g') from
      bmSDS_fromBlocks_eq_J m g', ← h.2.2.2.2.2.2.1 b₁ b₂, hb₁eq, hb₂eq]
    simpa only [bmSDS_B, Matrix.toBilin'_apply'] using horth
  exact ⟨b₁, b₂, hb₁eq, hb₂eq, hb₁, hb₂, hbLi, hbOrth⟩

private lemma bmSDS_siegel_plane_partner (m g' : ℕ)
    (b₁ b₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hli : LinearIndependent (GaloisField 2 g') ![b₁, b₂])
    (horth : b₁ ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') b₂) = 0) :
    ∃ (hm2 : 2 ≤ m) (b₁' b₂' : (Fin m ⊕ Fin m) → GaloisField 2 g'),
      b₁ ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') b₁') = 1 ∧
      b₂ ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') b₂') = 1 ∧
      b₁' ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') b₂') = 0 ∧
      b₁ ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') b₂') = 0 ∧
      b₂ ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') b₁') = 0 := by
  have hB : (bmSDS_B m g').IsAlt := bmSDS_B_isAlt m g'
  have hnd : (bmSDS_B m g').Nondegenerate := bmSDS_B_nondegenerate m g'
  have h12 : bmSDS_B m g' b₁ b₂ = 0 := by
    rw [bmSDS_B, Matrix.toBilin'_apply']
    exact horth
  obtain ⟨m0, b, hsymp, hb1, hb2, hdim⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.alternating_isotropic_pair_extension
      (K := GaloisField 2 g') (V := Fin m ⊕ Fin m → GaloisField 2 g') hB hnd hli h12
  have hpair : ∀ x y : Fin (m0 + 2) ⊕ Fin (m0 + 2),
      bmSDS_B m g' (b x) (b y) = (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin (m0 + 2) ⊕ Fin (m0 + 2)) (Fin (m0 + 2) ⊕ Fin (m0 + 2))
          (GaloisField 2 g')) x y := by
    intro x y
    have hh := congrFun₂ hsymp x y
    rwa [LinearMap.BilinForm.toMatrix_apply] at hh
  have hfin : Module.finrank (GaloisField 2 g') (Fin m ⊕ Fin m → GaloisField 2 g') = m + m := by
    rw [Module.finrank_eq_card_basis (Pi.basisFun (GaloisField 2 g') (Fin m ⊕ Fin m)),
      Fintype.card_sum, Fintype.card_fin]
  have hm2 : 2 ≤ m := by omega
  let i0 : Fin (m0 + 2) := ⟨0, by omega⟩
  let i1 : Fin (m0 + 2) := ⟨1, by omega⟩
  refine ⟨hm2, b (Sum.inr i0), b (Sum.inr i1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hb1]
    have hp := hpair (Sum.inl i0) (Sum.inr i0)
    rw [bmSDS_B, Matrix.toBilin'_apply'] at hp
    exact hp.trans (by simp [Matrix.fromBlocks, i0])
  · rw [← hb2]
    have hp := hpair (Sum.inl i1) (Sum.inr i1)
    rw [bmSDS_B, Matrix.toBilin'_apply'] at hp
    exact hp.trans (by simp [Matrix.fromBlocks, i0, i1])
  · have hp := hpair (Sum.inr i0) (Sum.inr i1)
    rw [bmSDS_B, Matrix.toBilin'_apply'] at hp
    exact hp.trans (by simp [Matrix.fromBlocks, i0, i1])
  · rw [← hb1]
    have hp := hpair (Sum.inl i0) (Sum.inr i1)
    rw [bmSDS_B, Matrix.toBilin'_apply'] at hp
    exact hp.trans (by simp [Matrix.fromBlocks, i0, i1])
  · rw [← hb2]
    have hp := hpair (Sum.inl i1) (Sum.inr i0)
    rw [bmSDS_B, Matrix.toBilin'_apply'] at hp
    exact hp.trans (by simp [Matrix.fromBlocks, i0, i1])

private lemma bmSDS_model_siegel_conj
    (m g' : ℕ)
    (b₁ b₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (hli : LinearIndependent (GaloisField 2 g') ![b₁, b₂])
    (horth : b₁ ⬝ᵥ (Matrix.mulVec (bmSDS_J m g') b₂) = 0) :
    ∃ (β : Fin (ggU .PSp m g').D.rank → ℤ) (u : (ggU .PSp m g').K),
      β ∈ (ggU .PSp m g').D.roots ∧ GGShortTag .PSp ∧ 2 • β ∉ (ggU .PSp m g').D.roots ∧
      ((((ggU .PSp m g').D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
          (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype) =
        altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 g')) b₁ b₂ := by
  obtain ⟨hm2, b₁', b₂', hp₁, hp₂, hpq, hq₁, hq₂⟩ :=
    bmSDS_siegel_plane_partner m g' b₁ b₂ hli horth
  obtain ⟨β, hβ, h2β, u, hconj, -⟩ :=
    exists_conj_rootGroup_eq_altSiegelGroup_PSp m (GaloisField 2 g') hm2 b₁ b₂ b₁' b₂'
      hp₁ hp₂ ⟨horth, hpq, hq₁, hq₂⟩
  refine ⟨β, u, hβ, Or.inl rfl, h2β, ?_⟩
  have hconj' : (Subgroup.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype
      (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u))
        ((ggU .PSp m g').D.rootGroup β))) =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 g')) b₁ b₂ := hconj
  rw [bmSDS_fromBlocks_eq_J m g'] at hconj'
  exact hconj'

private lemma bmSDS_closure_siegel_transport
    (n f m g' : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r ι ext)
    (b₁ b₂ : (Fin m ⊕ Fin m) → GaloisField 2 g')
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (hb₁eq : ext b₁ = a₁) (hb₂eq : ext b₂ = a₂)
    (u : (ggU .PSp m g').K)
    {β : Fin (ggU .PSp m g').D.rank → ℤ}
    (hconj : (Subgroup.map (CFSG.Open.StatedSp m (GaloisField 2 g')).subtype
        (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u))
          ((ggU .PSp m g').D.rootGroup β))) =
      altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 g')) b₁ b₂) :
    ((((ggU .PSp m g').D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
      altSiegelGroup (bmSDS_J n f) a₁ a₂ := by
  have htr := bmSDS_transport_altSiegel n f m g' r ι ext S e h
    (((ggU .PSp m g').D.rootGroup β).map (MulAut.conj u).toMonoidHom) b₁ b₂ hconj
  rw [htr, hb₁eq, hb₂eq]

private theorem bmSDS_closure_short
    (n f m g' : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅bmSDS_Ge S e, bmSDS_Ge S e⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6)))
    (ι : (ggU .PSp m g').K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hrange : ι.range = bmSDS_Ge S e)
    (r : GaloisField 2 g' ≃+* GaloisField 2 f)
    (ext : ((Fin m ⊕ Fin m) → GaloisField 2 g') → ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (h : bmSDS_IsBlockEmb n f m g' S e r ι ext)
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (horth : a₁ ⬝ᵥ (Matrix.mulVec (bmSDS_J n f) a₂) = 0)
    (hle : altSiegelGroup (bmSDS_J n f) a₁ a₂ ≤
      J'.map ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)) :
    ∃ (β : Fin (ggU .PSp m g').D.rank → ℤ) (u : (ggU .PSp m g').K),
      β ∈ (ggU .PSp m g').D.roots ∧ GGShortTag .PSp ∧ 2 • β ∉ (ggU .PSp m g').D.roots ∧
      ((((ggU .PSp m g').D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        altSiegelGroup (bmSDS_J n f) a₁ a₂ := by
  have hm : 1 ≤ m := bmSDS_one_le_m hJe ι hrange
  obtain ⟨b₁, b₂, hb₁eq, hb₂eq, hb₁, hb₂, hbLi, hbOrth⟩ :=
    bmSDS_closure_siegel_plane_mem n f m g' S hS he hadj hdeg hJe hA6 ι r ext h
      a₁ a₂ ha₁ ha₂ hli horth hle
  obtain ⟨β, u, hβ, hshort, h2β, hconj⟩ :=
    bmSDS_model_siegel_conj m g' b₁ b₂ hbLi hbOrth
  exact ⟨β, u, hβ, hshort, h2β,
    bmSDS_closure_siegel_transport n f m g' S ι r ext h
      b₁ b₂ a₁ a₂ hb₁eq hb₂eq u hconj⟩

private lemma bmSDSx_embedding_f
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (bmSDS_A S) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSDS_J n f) e = e)
    (hdeg : blockDegree (bmSDS_A S) e < 2) :
    ∃ (m : ℕ) (iota : (ggU .PSp m f).K →* CFSG.Open.StatedSp n (GaloisField 2 f))
      (ext : ((Fin m ⊕ Fin m) → GaloisField 2 f) →
        ((Fin n ⊕ Fin n) → GaloisField 2 f)),
      Module.finrank (GaloisField 2 f) (bmSDS_W e) = m + m ∧
      (∀ y, iota y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
        y ∈ Subgroup.center (ggU .PSp m f).K) ∧
      bmSDS_IsBlockEmb n f m f S e (RingEquiv.refl (GaloisField 2 f)) iota ext := by
  obtain ⟨m, iota, hi, hr, hc, hfin, φ, hsp, htrans⟩ :=
    bmSDS_blockGroup_iso_ext n f S hS he hadj hdeg
  have h1 : 1 ≤ f ∨ f = 0 := by
    rcases Nat.eq_zero_or_pos f with hf | hf
    · exact Or.inr hf
    · exact Or.inl (by omega)
  have hcore : (1 ≤ f ∨ f = 0) ∧ Function.Injective iota ∧ iota.range = bmSDS_Ge S e ∧
      (∀ y, iota y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
        y ∈ Subgroup.center (ggU .PSp m f).K) ∧
      Function.Injective (fun u : (Fin m ⊕ Fin m) → GaloisField 2 f =>
        (↑(φ.symm u) : (Fin n ⊕ Fin n) → GaloisField 2 f)) ∧
      (∀ v, v ∈ bmSDS_W e ↔
        ∃ u, (↑(φ.symm u) : (Fin n ⊕ Fin n) → GaloisField 2 f) = v) ∧
      (∀ u u', (↑(φ.symm (u + u')) : (Fin n ⊕ Fin n) → GaloisField 2 f) =
        ↑(φ.symm u) + ↑(φ.symm u')) ∧
      (∀ c u, (↑(φ.symm (c • u)) : (Fin n ⊕ Fin n) → GaloisField 2 f) =
        (RingEquiv.refl (GaloisField 2 f)) c • ↑(φ.symm u)) ∧
      (∀ u u', bmSDS_B n f (↑(φ.symm u)) (↑(φ.symm u')) =
        (RingEquiv.refl (GaloisField 2 f))
          (u ⬝ᵥ Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 f)) u')) := by
    refine ⟨h1, hi, hr, hc, ?_, ?_, ?_, ?_, ?_⟩
    · intro u u' h
      exact φ.symm.injective (Subtype.ext h)
    · intro v
      constructor
      · intro hv
        exact ⟨φ ⟨v, hv⟩, congrArg Subtype.val (φ.symm_apply_apply ⟨v, hv⟩)⟩
      · rintro ⟨u, rfl⟩
        exact (φ.symm u).2
    · intro u u'
      exact congrArg Subtype.val (map_add φ.symm u u')
    · intro c u
      exact (congrArg Subtype.val (map_smul φ.symm c u)).trans rfl
    · intro u u'
      rw [show bmSDS_B n f (↑(φ.symm u)) (↑(φ.symm u')) =
          ((bmSDS_B n f).restrict (bmSDS_W e)) (φ.symm u) (φ.symm u') from rfl]
      rw [hsp (φ.symm u) (φ.symm u'), φ.apply_symm_apply, φ.apply_symm_apply]
      rw [show (CFSG.RankThree.SubgroupLists.spForm m (GaloisField 2 f)) u u' =
          (CFSG.RankThree.Classical.spForm m (GaloisField 2 f)) u u' from rfl]
      rw [CFSG.RankThree.Classical.spForm_apply]
      have hgram : CFSG.ClassicalInvolution.Models.SymplecticPairs.gram (GaloisField 2 f) m =
          Matrix.J (Fin m) (GaloisField 2 f) := by
        rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_eq_neg_J]
        ext i j
        rw [Matrix.neg_apply, CharTwo.neg_eq]
      rw [hgram]
      rfl
  have h6 : ∀ g u, Matrix.mulVec (bmSDS_matN n f (iota g)) (↑(φ.symm u)) =
      ↑(φ.symm (Matrix.mulVec (bmSDS_matM m f g) u)) := by
    intro g u
    rw [htrans g (φ.symm u), φ.apply_symm_apply]
  obtain ⟨-, h7, h8, h9⟩ :=
    bmSDS_embedding_compat n f m f S e he hadj (RingEquiv.refl (GaloisField 2 f)) iota
      (fun u => ↑(φ.symm u)) h6 hcore
  obtain ⟨-, -, -, -, hext, hv, hadd, hsemi, hiso⟩ := hcore
  exact ⟨m, iota, (fun u => ↑(φ.symm u)), hfin, hc,
    ⟨hi, hr, hext, hv, hadd, hsemi, hiso, h6, h7, h8, h9⟩⟩

theorem exists_blockModel_selfDual_PSp_explicit
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e) (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    ∃ (r : ℕ)
      (ι : (ggU .PSp r f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (β₀ : Fin (ggU .PSp r f).D.rank → ℤ), 2 * r = Module.finrank (GaloisField 2 f)
          (LinearMap.range (Matrix.toLin' e)) ∧
      GGLongRoot (ggU .PSp r f).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) → y ∈ Subgroup.center
        (ggU .PSp r f).K) ∧ ι.range = J' ∧
      ∃ v w : (Fin n ⊕ Fin n) → (GaloisField 2 f), v ⬝ᵥ Matrix.mulVec
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) w
        = 1 ∧
        (((ggU .PSp r f).D.rootGroup β₀).map ι).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) = matTransvGroup v
        (Matrix.mulVec
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)
        ∧
        (((ggU .PSp r f).D.rootGroup (-β₀)).map ι).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) = matTransvGroup w
        (Matrix.mulVec
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) w)
            := by
  obtain ⟨m, ι, ext, hfin, hcent, h⟩ := bmSDSx_embedding_f n f S hS he hadj hdeg
  have hrange : ι.range = bmSDS_Ge S e := h.2.1
  have hcomp : J' = bmSDS_Ge S e :=
    bmSDS_component_eq_no_small n f S hS he hadj hdeg
      (bmSDS_blockGroup_dim_two n f S he hadj)
      (bmSDS_frozen1_hK n f S hS he hadj hdeg hJe hA6) hJe
  have hT := bmSDS_hT_gen n f m f S ι (RingEquiv.refl (GaloisField 2 f)) ext h
  have hneg := bmSDS_hneg_gen n f m f S ι (RingEquiv.refl (GaloisField 2 f)) ext h
  obtain ⟨β₀, v, w, hlong, hvw, hX, hX'⟩ :=
    bmSDS_frozen1_root_pkg n f m f S hJe ι hrange hT hneg
  have hrank : 2 * m = Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e)) := by
    have hW : LinearMap.range (Matrix.toLin' e) = bmSDS_W e := by
      rw [Matrix.toLin'_apply']
    rw [hW, hfin]
    omega
  exact ⟨m, ι, β₀, hrank, hlong, hcent, by rw [hrange, hcomp], v, w, hvw, hX, hX'⟩

theorem exists_blockModelClosure_selfDual_PSp_explicit
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e) (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    ∃ (r : ℕ) (ι : (ggU .PSp r f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2
        f))),
      2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) ∧
      (∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) → y ∈ Subgroup.center
          (ggU .PSp r f).K) ∧
      ι.range = J' ∧
      (∀ v₀ : (Fin n ⊕ Fin n) → GaloisField 2 f, v₀ ≠ 0 → matTransvGroup v₀ (Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          v₀) ≤ J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
        ∃ (β : Fin (ggU .PSp r f).D.rank → ℤ) (u : (ggU .PSp r f).K), β ∈ (ggU .PSp r f).D.roots ∧
            GGLongRoot (ggU .PSp r f).D β ∧
          ((((ggU .PSp r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
              (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype = matTransvGroup v₀ (Matrix.mulVec
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2
              f)) v₀)) ∧
      (∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 → LinearIndependent
          (GaloisField 2 f) ![a₁, a₂] → a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix
          (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 → altSiegelGroup
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          a₁ a₂ ≤ J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
        ∃ (β : Fin (ggU .PSp r f).D.rank → ℤ) (u : (ggU .PSp r f).K), β ∈ (ggU .PSp r f).D.roots ∧
            GGShortTag .PSp ∧ 2 • β ∉ (ggU .PSp r f).D.roots ∧
          ((((ggU .PSp r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
              (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype = altSiegelGroup (Matrix.fromBlocks
              0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂) := by
  obtain ⟨m, ι, ext, hfin, hcent, h⟩ := bmSDSx_embedding_f n f S hS he hadj hdeg
  have hrange : ι.range = bmSDS_Ge S e := h.2.1
  have hcomp : J' = bmSDS_Ge S e :=
    bmSDS_component_eq_no_small n f S hS he hadj hdeg
      (bmSDS_blockGroup_dim_two n f S he hadj)
      (bmSDS_frozen1_hK n f S hS he hadj hdeg hJe hA6) hJe
  have hrank : 2 * m = Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e)) := by
    have hW : LinearMap.range (Matrix.toLin' e) = bmSDS_W e := by
      rw [Matrix.toLin'_apply']
    rw [hW, hfin]
    omega
  refine ⟨m, ι, hrank, hcent, by rw [hrange, hcomp], ?_, ?_⟩
  · intro v₀ hv₀ hle
    exact bmSDS_closure_long n f m f S hS he hadj hdeg hJe hA6 ι hrange
      (RingEquiv.refl (GaloisField 2 f)) ext h v₀ hv₀ hle
  · intro a₁ a₂ ha₁ ha₂ hli horth hle
    exact bmSDS_closure_short n f m f S hS he hadj hdeg hJe hA6 ι hrange
      (RingEquiv.refl (GaloisField 2 f)) ext h a₁ a₂ ha₁ ha₂ hli horth hle

private lemma bmSDSf_card_ne_three (f : ℕ) : Nat.card (GaloisField 2 f) ≠ 3 := by
  intro h3
  rcases Nat.lt_or_ge f 2 with hf | hf
  · rw [bmSDS_blockGroup_card_small f (by omega)] at h3
    omega
  · have h4 := bmSDS_blockGroup_card_large f hf
    omega

theorem exists_blockModel_selfDual_PSp_explicitFwd
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e) (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    ∃ (r : ℕ) (ι : (ggU .PSp r f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f))),
      2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) ∧
      1 ≤ r ∧ (4 ≤ Nat.card (GaloisField 2 f) ∨ 3 ≤ r) ∧ Function.Injective ι ∧
      (∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) → y ∈ Subgroup.center
          (ggU .PSp r f).K) ∧
      ι.range = J' ∧
      ∀ (β : Fin (ggU .PSp r f).D.rank → ℤ) (u : (ggU .PSp r f).K), β ∈ (ggU .PSp r f).D.roots →
        (GGLongRoot (ggU .PSp r f).D β →
          ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
            ((((ggU .PSp r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
                (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
              matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∧
        (¬ GGLongRoot (ggU .PSp r f).D β →
          ∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
            LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
            a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
            ((((ggU .PSp r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
                (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
              altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂) := by
  obtain ⟨m, ι, ext, hfin, hcent, h⟩ := bmSDSx_embedding_f n f S hS he hadj hdeg
  have hrange : ι.range = bmSDS_Ge S e := h.2.1
  have hcomp : J' = bmSDS_Ge S e :=
    bmSDS_component_eq_no_small n f S hS he hadj hdeg
      (bmSDS_blockGroup_dim_two n f S he hadj)
      (bmSDS_frozen1_hK n f S hS he hadj hdeg hJe hA6) hJe
  have hrank : 2 * m = Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e)) := by
    have hW : LinearMap.range (Matrix.toLin' e) = bmSDS_W e := by
      rw [Matrix.toLin'_apply']
    rw [hW, hfin]
    omega
  have hm : 1 ≤ m := bmSDS_one_le_m hJe ι hrange
  have hfield : 4 ≤ Nat.card (GaloisField 2 f) ∨ 3 ≤ m := by
    rcases bmSDS_frozen1_hK n f S hS he hadj hdeg hJe hA6 with h4 | ⟨h3, _⟩ | ⟨_, h6⟩
    · exact Or.inl h4
    · exact absurd h3 (bmSDSf_card_ne_three f)
    · refine Or.inr ?_
      rw [bmSDS_orthogonal_W' (n := n) (f := f) he.2.1 hadj] at h6
      omega
  have hext0 : ext 0 = 0 := by
    have h : ext 0 = ext 0 + ext 0 := by simpa using h.2.2.2.2.1 0 0
    exact add_left_cancel (h.symm.trans (add_zero (ext 0)).symm)
  have hext_ne : ∀ u, u ≠ 0 → ext u ≠ 0 := by
    intro u hu h0
    exact hu (h.2.2.1 (h0.trans hext0.symm))
  have hli_ext : ∀ a₁ a₂ : (Fin m ⊕ Fin m) → GaloisField 2 f,
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      LinearIndependent (GaloisField 2 f) ![ext a₁, ext a₂] := by
    intro a₁ a₂ hli
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro c₁ c₂ hc
    have hz : ext (c₁ • a₁ + c₂ • a₂) = 0 := by
      rw [h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.1]
      simpa using hc
    exact hli c₁ c₂ (h.2.2.1 (hz.trans hext0.symm))
  refine ⟨m, ι, hrank, hm, hfield, h.1, hcent, by rw [hrange, hcomp], ?_⟩
  intro β u hβ
  constructor
  · intro hl
    obtain ⟨v₀, hv₀, hX⟩ := exists_matTransvGroup_eq_rootGroup_PSp m f hβ hl u
    have hX' : (((ggU .PSp m f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp m (GaloisField 2 f)).subtype =
        matTransvGroup v₀ (Matrix.mulVec (Matrix.J (Fin m) (GaloisField 2 f)) v₀) := by
      rw [hX, bmSDS_fromBlocks_eq_J m f]
    exact ⟨ext v₀, hext_ne v₀ hv₀,
      bmSDS_transport_rootGroup n f m f (RingEquiv.refl (GaloisField 2 f)) ι ext S e h
        (((ggU .PSp m f).D.rootGroup β).map (MulAut.conj u).toMonoidHom) v₀ hX'⟩
  · intro hnl
    obtain ⟨a₁, a₂, ha₁, ha₂, hli, horth, hX⟩ :=
      exists_altSiegelGroup_eq_rootGroup_PSp m f hβ hnl u
    have hX' : (((ggU .PSp m f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp m (GaloisField 2 f)).subtype =
        altSiegelGroup (Matrix.J (Fin m) (GaloisField 2 f)) a₁ a₂ := by
      rw [hX, bmSDS_fromBlocks_eq_J m f]
    have horth' : ext a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (ext a₂) = 0 := by
      have hB := h.2.2.2.2.2.2.1 a₁ a₂
      rw [bmSDS_B, Matrix.toBilin'_apply', RingEquiv.refl_apply,
        ← bmSDS_fromBlocks_eq_J m f] at hB
      rw [horth] at hB
      simpa only [bmSDS_J] using hB
    exact ⟨ext a₁, ext a₂, hext_ne a₁ ha₁, hext_ne a₂ ha₂, hli_ext a₁ a₂ hli, horth',
      bmSDS_transport_altSiegel n f m f (RingEquiv.refl (GaloisField 2 f)) ι ext S e h
        (((ggU .PSp m f).D.rootGroup β).map (MulAut.conj u).toMonoidHom) a₁ a₂ hX'⟩

theorem exists_linearBlockModel_selfDual_PSp
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    ∃ (m : ℕ) (ι : (ggU .PSp m f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (E : ((Fin m ⊕ Fin m) → GaloisField 2 f) →ₗ[GaloisField 2 f]
        ((Fin n ⊕ Fin n) → GaloisField 2 f))
      (W : Submodule (GaloisField 2 f) ((Fin n ⊕ Fin n) → GaloisField 2 f)),
      1 ≤ m ∧ (4 ≤ Nat.card (GaloisField 2 f) ∨ 3 ≤ m) ∧ Function.Injective ι ∧
      ι.range = J' ∧ Function.Injective E ∧
      (∀ x y, x ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 f)).mulVec y =
        E x ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec (E y)) ∧
      (∀ (g : (ggU .PSp m f).K) x,
        (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (ι g) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ (E x)) =
          E (((CFSG.Open.StatedSp m (GaloisField 2 f)).subtype g :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 f)) *ᵥ x)) ∧
      (∀ (g : (ggU .PSp m f).K) w, w ∈ W →
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (ι g) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ w = w) ∧
      (∀ v, ∃ x, ∃ w ∈ W, v = E x + w) ∧
      (∀ x w, w ∈ W → E x ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec w = 0) := by
  obtain ⟨m, ι, ext, _hfin, _hcent, h⟩ := bmSDSx_embedding_f n f S hS he hadj hdeg
  have hrange : ι.range = bmSDS_Ge S e := h.2.1
  have hcomp : J' = bmSDS_Ge S e :=
    bmSDS_component_eq_no_small n f S hS he hadj hdeg
      (bmSDS_blockGroup_dim_two n f S he hadj)
      (bmSDS_frozen1_hK n f S hS he hadj hdeg hJe hA6) hJe
  have hm : 1 ≤ m := bmSDS_one_le_m hJe ι hrange
  have hfield : 4 ≤ Nat.card (GaloisField 2 f) ∨ 3 ≤ m := by
    rcases bmSDS_frozen1_hK n f S hS he hadj hdeg hJe hA6 with h4 | ⟨h3, _⟩ | ⟨_, h6⟩
    · exact Or.inl h4
    · exact absurd h3 (bmSDSf_card_ne_three f)
    · refine Or.inr ?_
      rw [bmSDS_orthogonal_W' (n := n) (f := f) he.2.1 hadj] at h6
      omega
  obtain ⟨hi, _hr, hExt, _hRange, hAdd, hSmul, hIso, hAct, hFix, hSplit, hOrth⟩ := h
  let E : ((Fin m ⊕ Fin m) → GaloisField 2 f) →ₗ[GaloisField 2 f]
      ((Fin n ⊕ Fin n) → GaloisField 2 f) :=
    { toFun := ext
      map_add' := hAdd
      map_smul' := fun c x => by simpa only [RingEquiv.refl_apply, RingHom.id_apply] using hSmul c x }
  refine ⟨m, ι, E, bmSDS_W (1 - e), hm, hfield, hi, by rw [hrange, hcomp], hExt, ?_, ?_,
    hFix, hSplit, ?_⟩
  · intro x y
    have hI := hIso x y
    rw [bmSDS_B, Matrix.toBilin'_apply', RingEquiv.refl_apply,
      ← bmSDS_fromBlocks_eq_J m f] at hI
    exact hI.symm
  · exact hAct
  · intro x w hw
    have hO := hOrth x w hw
    rw [bmSDS_B, Matrix.toBilin'_apply'] at hO
    exact hO

end CFSG.StandardType.ClassicalPosition
