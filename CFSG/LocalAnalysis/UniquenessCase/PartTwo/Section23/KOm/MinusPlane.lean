module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.Isometry
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaMinusFour
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Orthogonal.LineStabilizer
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LieType.Universal.SpinCenterMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusVectors
import CFSG.Timmesfeld.Orders.ClassicalAnisotropic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix
open QuadraticMap
open CFSG.ClassicalGroups.Orthogonal (rootGroupGL lineStabilizer mem_lineStabilizer_iff
  mem_rootGroupGL_iff polar_map_of_linearIsometry polar_smul_right_eq toLinEquiv
  toLinEquiv_apply)
open CFSG.LieType.Universal.Spin (quadMinus binaryForm coe_quadMinus
  polar_quadMinus_single_inl polar_quadMinus_single_inr_inr_zero
  polar_quadMinus_single_inr_inr_one binaryForm_apply quadMinus_apply
  nondegenerate_polarBilin_quadMinus_of_finite)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def planeBlock (A : Matrix ιM ιM K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => A (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j))

private def planeBasis (k : Fin 2) : ιM → K
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr i) => if i = k then 1 else 0

private theorem sum_ιM (f : ιM → K) :
    ∑ i, f i = f (Sum.inl 0) + f (Sum.inr (Sum.inl 0)) +
      (f (Sum.inr (Sum.inr 0)) + f (Sum.inr (Sum.inr 1))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two,
    Fin.sum_univ_one]
  ring

theorem e1M_apply_plane (i : Fin 2) :
    KTabC.e1M K (Sum.inr (Sum.inr i)) = 0 := by
  rw [KTabC.e1M]
  exact Pi.single_eq_of_ne (M := fun _ : ιM => K)
    (by simp : (Sum.inr (Sum.inr i) : ιM) ≠ Sum.inl 0) (1 : K)

private theorem lineStabilizer_lam_ne_zero {A : GL ιM K} {lam : K}
    (hcol : (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = lam • KTabC.e1M K) : lam ≠ 0 := by
  intro h0
  have hz : (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = 0 := by rw [hcol, h0, zero_smul]
  have hdet : (A : Matrix ιM ιM K).det ≠ 0 :=
    Matrix.det_ne_zero_of_left_inverse (B := (A⁻¹ : GL ιM K)) (by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
  exact e1M_ne_zero (Matrix.eq_zero_of_mulVec_eq_zero hdet hz)

theorem lineStabilizer_apply_y {b c : K} {A : GL ιM K} {lam : K}
    (hiso : ∀ v, quadMinus 2 K b c ((A : Matrix ιM ιM K) *ᵥ v) = quadMinus 2 K b c v)
    (hcol : (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = lam • KTabC.e1M K) (hlam : lam ≠ 0)
    (v : ιM → K) :
    ((A : Matrix ιM ιM K) *ᵥ v) (Sum.inr (Sum.inl 0)) =
      lam⁻¹ * v (Sum.inr (Sum.inl 0)) := by
  have hmap : polar (quadMinus 2 K b c) ((A : Matrix ιM ιM K) *ᵥ v)
      ((A : Matrix ιM ιM K) *ᵥ KTabC.e1M K) =
      polar (quadMinus 2 K b c) v (KTabC.e1M K) := by
    have h := polar_map_of_linearIsometry (Q := quadMinus 2 K b c)
      (Q' := quadMinus 2 K b c) (toLinEquiv ιM K A)
      (fun x => by rw [toLinEquiv_apply]; exact hiso x) v (KTabC.e1M K)
    simpa only [toLinEquiv_apply] using h
  rw [hcol, polar_smul_right_eq] at hmap
  have hp1 : polar (quadMinus 2 K b c) ((A : Matrix ιM ιM K) *ᵥ v) (KTabC.e1M K) =
      ((A : Matrix ιM ιM K) *ᵥ v) (Sum.inr (Sum.inl 0)) := by
    change polar (quadMinus 2 K b c) ((A : Matrix ιM ιM K) *ᵥ v)
      (Pi.single (Sum.inl 0) 1) = _
    rw [polar_quadMinus_single_inl]
  have hp2 : polar (quadMinus 2 K b c) v (KTabC.e1M K) = v (Sum.inr (Sum.inl 0)) := by
    change polar (quadMinus 2 K b c) v (Pi.single (Sum.inl 0) 1) = _
    rw [polar_quadMinus_single_inl]
  rw [hp1, hp2] at hmap
  have h := congrArg (fun z => lam⁻¹ * z) hmap
  rwa [← mul_assoc, inv_mul_cancel₀ hlam, one_mul] at h

private theorem lineStabilizer_row_ne {b c : K} {A : GL ιM K} {lam : K}
    (hiso : ∀ v, quadMinus 2 K b c ((A : Matrix ιM ιM K) *ᵥ v) = quadMinus 2 K b c v)
    (hcol : (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = lam • KTabC.e1M K) (hlam : lam ≠ 0)
    {k : ιM} (hk : k ≠ Sum.inr (Sum.inl 0)) :
    (A : Matrix ιM ιM K) (Sum.inr (Sum.inl 0)) k = 0 := by
  have h := lineStabilizer_apply_y hiso hcol hlam (Pi.single k 1)
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_of_ne hk.symm, mul_zero] at h
  exact h

private theorem lineStabilizer_col_ne {A : GL ιM K} {lam : K}
    (hcol : (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = lam • KTabC.e1M K)
    {i : ιM} (hi : i ≠ Sum.inl 0) :
    (A : Matrix ιM ιM K) i (Sum.inl 0) = 0 := by
  have h := congrArg (fun v => v i) hcol
  simpa [KTabC.e1M, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, hi] using h

private theorem planeBlock_mul_entry {b c : K} {A B : GL ιM K}
    (hA : A ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K))
    (hB : B ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)) (i j : Fin 2) :
    ((A * B : GL ιM K) : Matrix ιM ιM K) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) =
      (planeBlock (A : Matrix ιM ιM K) * planeBlock (B : Matrix ιM ιM K)) i j := by
  obtain ⟨hisoA, lam, hcolA⟩ :=
    (mem_lineStabilizer_iff (Q := quadMinus 2 K b c)).mp hA
  obtain ⟨hisoB, mu, hcolB⟩ :=
    (mem_lineStabilizer_iff (Q := quadMinus 2 K b c)).mp hB
  have hmu := lineStabilizer_lam_ne_zero hcolB
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mul_apply,
    sum_ιM (fun k => (A : Matrix ιM ιM K) (Sum.inr (Sum.inr i)) k *
      (B : Matrix ιM ιM K) k (Sum.inr (Sum.inr j))), Fin.sum_univ_two]
  have hxA : (A : Matrix ιM ιM K) (Sum.inr (Sum.inr i)) (Sum.inl 0) = 0 :=
    lineStabilizer_col_ne hcolA (by simp)
  have hBy : (B : Matrix ιM ιM K) (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inr j)) = 0 :=
    lineStabilizer_row_ne hisoB hcolB hmu (by simp)
  simp only [planeBlock, Matrix.of_apply, hxA, hBy, zero_mul, mul_zero, zero_add]

theorem isoFix_le_lineStabilizer (b c : K) :
    isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) ≤
      lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K) := by
  intro A hA
  obtain ⟨hiso, hfix⟩ := (mem_isoFix).mp hA
  refine (mem_lineStabilizer_iff (Q := quadMinus 2 K b c)).mpr ⟨?_, 1, ?_⟩
  · intro v
    have h := hiso v
    rwa [← coe_quadMinus 2 K b c] at h
  · simpa using hfix

theorem planeBlock_mul {b c : K} {A B : GL ιM K}
    (hA : A ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K))
    (hB : B ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)) :
    planeBlock ((A * B : GL ιM K) : Matrix ιM ιM K) =
      planeBlock (A : Matrix ιM ιM K) * planeBlock (B : Matrix ιM ιM K) := by
  ext i j
  exact planeBlock_mul_entry hA hB i j

theorem mulVec_planeVec_apply (A : Matrix ιM ιM K) (p : Fin 2 → K) (i : Fin 2) :
    (A *ᵥ planeVec p) (Sum.inr (Sum.inr i)) = (planeBlock A *ᵥ p) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_ιM (fun k => A (Sum.inr (Sum.inr i)) k * planeVec p k), Fin.sum_univ_two]
  simp only [planeVec_inl, planeVec_inr_inl, planeVec_inr_inr, planeBlock, Matrix.of_apply,
    mul_zero, zero_add]

private theorem mulVec_planeBasis_apply (A : Matrix ιM ιM K) (k i : Fin 2) :
    (A *ᵥ planeBasis k) (Sum.inr (Sum.inr i)) =
      A (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr k)) := by
  simp only [Matrix.mulVec, dotProduct]
  fin_cases k <;> fin_cases i <;> simp [planeBasis]

private theorem mulVec_planeVec_y {b c : K} {A : GL ιM K} {lam : K}
    (hiso : ∀ v, quadMinus 2 K b c ((A : Matrix ιM ιM K) *ᵥ v) = quadMinus 2 K b c v)
    (hcol : (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = lam • KTabC.e1M K) (hlam : lam ≠ 0)
    (p : Fin 2 → K) : ((A : Matrix ιM ιM K) *ᵥ planeVec p) (Sum.inr (Sum.inl 0)) = 0 := by
  rw [lineStabilizer_apply_y hiso hcol hlam]
  simp only [planeVec_inr_inl, mul_zero]

private theorem quadMinus_mulVec_planeVec {b c : K} {A : GL ιM K} {lam : K}
    (hiso : ∀ v, quadMinus 2 K b c ((A : Matrix ιM ιM K) *ᵥ v) = quadMinus 2 K b c v)
    (hcol : (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = lam • KTabC.e1M K) (hlam : lam ≠ 0)
    (p : Fin 2 → K) :
    quadMinus 2 K b c ((A : Matrix ιM ιM K) *ᵥ planeVec p) =
      binaryForm K b c (planeBlock (A : Matrix ιM ιM K) *ᵥ p) := by
  rw [quadMinus_apply, binaryForm_apply, Fin.sum_univ_one]
  rw [mulVec_planeVec_y hiso hcol hlam, mulVec_planeVec_apply, mulVec_planeVec_apply]
  ring

theorem binaryForm_planeBlock_mulVec {b c : K} {A : GL ιM K}
    (hA : A ∈ lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)) (p : Fin 2 → K) :
    binaryForm K b c (planeBlock (A : Matrix ιM ιM K) *ᵥ p) = binaryForm K b c p := by
  obtain ⟨hiso, lam, hcol⟩ := (mem_lineStabilizer_iff (Q := quadMinus 2 K b c)).mp hA
  have hlam := lineStabilizer_lam_ne_zero hcol
  rw [← quadMinus_planeVec b c p, ← quadMinus_mulVec_planeVec hiso hcol hlam p]
  exact hiso (planeVec p)

theorem polar_e1M_eq_y {b c : K} (v : ιM → K) :
    polar (quadMinus 2 K b c) (KTabC.e1M K) v = v (Sum.inr (Sum.inl 0)) := by
  rw [polar_comm]
  change polar (quadMinus 2 K b c) v (Pi.single (Sum.inl 0) 1) = _
  rw [polar_quadMinus_single_inl]

theorem isoFix_isometry {b c : K} {A : GL ιM K}
    (hA : A ∈ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) :
    ∀ v, quadMinus 2 K b c ((A : Matrix ιM ιM K) *ᵥ v) = quadMinus 2 K b c v := by
  intro v
  have h := ((mem_isoFix).mp hA).1 v
  rwa [← coe_quadMinus 2 K b c] at h

theorem mulVec_apply_plane {b c : K} {A : GL ιM K} {lam : K}
    (hcol : (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = lam • KTabC.e1M K)
    {x : ιM → K} (hx : x (Sum.inr (Sum.inl 0)) = 0) (i : Fin 2) :
    ((A : Matrix ιM ιM K) *ᵥ x) (Sum.inr (Sum.inr i)) =
      (planeBlock (A : Matrix ιM ιM K) *ᵥ fun j => x (Sum.inr (Sum.inr j))) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_ιM (fun k => (A : Matrix ιM ιM K) (Sum.inr (Sum.inr i)) k * x k),
    Fin.sum_univ_two]
  have hAx : (A : Matrix ιM ιM K) (Sum.inr (Sum.inr i)) (Sum.inl 0) = 0 :=
    lineStabilizer_col_ne hcol (by simp)
  simp only [hAx, hx, planeBlock, Matrix.of_apply, zero_mul, mul_zero, zero_add]

private theorem mulVec_apply_planeCoord_of_block_one {b c : K} {A : GL ιM K} {lam : K}
    (hcol : (A : Matrix ιM ιM K) *ᵥ KTabC.e1M K = lam • KTabC.e1M K)
    {x : ιM → K} (hx : x (Sum.inr (Sum.inl 0)) = 0)
    (hblk : planeBlock (A : Matrix ιM ιM K) = (1 : Matrix (Fin 2) (Fin 2) K))
    (i : Fin 2) :
    ((A : Matrix ιM ιM K) *ᵥ x) (Sum.inr (Sum.inr i)) = x (Sum.inr (Sum.inr i)) := by
  rw [mulVec_apply_plane (b := b) (c := c) (A := A) (lam := lam) (x := x) hcol hx,
    hblk]
  exact congrFun (Matrix.one_mulVec (fun j => x (Sum.inr (Sum.inr j)))) i

private theorem rootGroup_planeBlock_entry {b c : K} {A : GL ιM K}
    (hperp : ∀ x, polar (quadMinus 2 K b c) (KTabC.e1M K) x = 0 →
      ∃ s : K, (A : Matrix ιM ιM K) *ᵥ x - x = s • KTabC.e1M K) (i k : Fin 2) :
    (A : Matrix ιM ιM K) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr k)) =
      (if i = k then 1 else 0) := by
  have hpol : polar (quadMinus 2 K b c) (KTabC.e1M K) (planeBasis k) = 0 := by
    rw [polar_e1M_eq_y]
    simp [planeBasis]
  obtain ⟨s, hs⟩ := hperp _ hpol
  have hPi : (s • KTabC.e1M K) (Sum.inr (Sum.inr i)) = 0 := by
    simp [KTabC.e1M]
  have hb : planeBasis k (Sum.inr (Sum.inr i)) =
      (if i = k then (1 : K) else 0) := rfl
  have h := congrFun hs (Sum.inr (Sum.inr i))
  rw [Pi.sub_apply, mulVec_planeBasis_apply, hb, hPi] at h
  exact sub_eq_zero.mp h

theorem planeBlock_eq_one_iff [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {A : GL ιM K}
    (hA : A ∈ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) :
    planeBlock (A : Matrix ιM ιM K) = 1 ↔ A ∈ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) := by
  obtain ⟨hisoStated, hfix⟩ := (mem_isoFix).mp hA
  obtain ⟨hiso, lam, hcol⟩ :=
    (mem_lineStabilizer_iff (Q := quadMinus 2 K b c)).mp
      (isoFix_le_lineStabilizer b c hA)
  have hlam := lineStabilizer_lam_ne_zero hcol
  have hlam1 : lam = 1 := by
    have h : lam • KTabC.e1M K = (1 : K) • KTabC.e1M K := by
      rw [← hcol, hfix]
      simp
    have hx := congrFun h (Sum.inl 0)
    simpa [KTabC.e1M] using hx
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have hu : quadMinus 2 K b c (KTabC.e1M K) = 0 := by
    rw [quadMinus_apply, Fin.sum_univ_one]
    simp [KTabC.e1M]
  constructor
  · intro hblk
    refine (mem_rootGroupGL_iff hnd hu e1M_ne_zero).mpr ⟨isoFix_isometry hA, hfix, ?_, ?_⟩
    · intro x hx
      have hx' : x (Sum.inr (Sum.inl 0)) = 0 := by
        rw [polar_e1M_eq_y] at hx
        exact hx
      refine ⟨((A : Matrix ιM ιM K) *ᵥ x - x) (Sum.inl 0), ?_⟩
      funext i
      rcases i with i | i | i
      · have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
        subst hi
        simp [KTabC.e1M]
      · have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
        subst hi
        rw [Pi.sub_apply, lineStabilizer_apply_y hiso hcol hlam, hlam1, hx']
        simp [KTabC.e1M]
      · have hcoord : ((A : Matrix ιM ιM K) *ᵥ x) (Sum.inr (Sum.inr i)) =
            x (Sum.inr (Sum.inr i)) :=
          mulVec_apply_planeCoord_of_block_one (b := b) (c := c) hcol hx' hblk i
        have hrhs : ((((A : Matrix ιM ιM K) *ᵥ x - x) (Sum.inl 0)) • KTabC.e1M K)
            (Sum.inr (Sum.inr i)) = 0 := by
          rw [Pi.smul_apply, e1M_apply_plane, smul_zero]
        rw [Pi.sub_apply, hcoord, hrhs, sub_self]
    · intro x
      rw [polar_e1M_eq_y, Pi.sub_apply, lineStabilizer_apply_y hiso hcol hlam, hlam1]
      simp
  · intro hroot
    obtain ⟨-, -, hperp, -⟩ := (mem_rootGroupGL_iff hnd hu e1M_ne_zero).mp hroot
    ext i j
    simpa only [planeBlock, Matrix.of_apply, Matrix.one_apply] using
      rootGroup_planeBlock_entry hperp i j

private noncomputable def planeBlockHom (b c : K) :
    ↥(lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)) →*
      Matrix (Fin 2) (Fin 2) K where
  toFun A := planeBlock (A.1 : Matrix ιM ιM K)
  map_one' := by
    ext i j
    simp [planeBlock, Matrix.one_apply]
  map_mul' A B := planeBlock_mul A.2 B.2

noncomputable def planeHom (b c : K) :
    ↥(lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K)) →* GL (Fin 2) K :=
  (planeBlockHom b c).toHomUnits

theorem coe_planeHom (b c : K) (g : ↥(lineStabilizer (quadMinus 2 K b c) (KTabC.e1M K))) :
    ((planeHom b c g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      planeBlock (g.1 : Matrix ιM ιM K) := by
  rw [planeHom]
  rfl

private noncomputable def planeBlockGHom (b c : K) {E : Subgroup (GL ιM K)}
    (hE : E ≤ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) :
    ↥E →* GL (Fin 2) K :=
  (planeHom b c).comp (Subgroup.inclusion (hE.trans (isoFix_le_lineStabilizer b c)))

private theorem planeBlockGHom_apply {b c : K} {E : Subgroup (GL ιM K)}
    (hE : E ≤ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) (g : ↥E) :
    ((planeBlockGHom b c hE g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      planeBlock (g.1 : Matrix ιM ιM K) := rfl

private theorem planeBlockGHom_eq_one_iff {b c : K} {E : Subgroup (GL ιM K)}
    (hE : E ≤ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) (g : ↥E) :
    planeBlockGHom b c hE g = 1 ↔ planeBlock (g.1 : Matrix ιM ιM K) = 1 := by
  constructor
  · intro h
    have h' : ((planeBlockGHom b c hE g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (1 : Matrix (Fin 2) (Fin 2) K) := by rw [h]; simp
    simpa only [planeBlockGHom_apply, Units.val_one] using h'
  · intro h
    rw [Units.ext_iff]
    simpa only [planeBlockGHom_apply, Units.val_one] using h

private theorem pow_two_le_two_of_dvd_two_mul_odd {k n : ℕ} (hn : Odd n)
    (h : 2 ^ k ∣ 2 * n) : 2 ^ k ≤ 2 := by
  rcases k with _ | _ | k
  · simp
  · simp
  · exfalso
    have h4 : 4 ∣ 2 ^ (k + 2) := by
      rw [pow_add]
      norm_num
    have h42 : 4 ∣ 2 * n := h4.trans h
    obtain ⟨t, ht⟩ := h42
    have hn2 : 2 ∣ n := by
      refine ⟨t, ?_⟩
      have h2 : 2 * n = 2 * (2 * t) := by rw [ht]; ring
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) h2
    exact hn.not_two_dvd_nat hn2

private theorem binaryForm_anisotropic {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ x : Fin 2 → K, x ≠ 0 → binaryForm K b c x ≠ 0 := by
  intro x hx h0
  rw [binaryForm_apply] at h0
  obtain ⟨h0', h1'⟩ :=
    CFSG.ClassicalGroups.Orthogonal.binary_eq_zero_of_irreducible (b := b) (c := c) hirr h0
  exact hx (funext fun i => by fin_cases i <;> assumption)

theorem card_le_two_mul_card_inf_rootGroupGL [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {E : Subgroup (GL ιM K)}
    (hE : E ≤ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K)) (hE2 : IsPGroup 2 ↥E) :
    Nat.card ↥E ≤ 2 * Nat.card ↥(E ⊓ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  set φ := planeBlockGHom b c hE with hφ
  have hker : φ.ker = (E ⊓ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)).subgroupOf E := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hφ,
      planeBlockGHom_eq_one_iff]
    constructor
    · intro h
      exact ⟨g.2, (planeBlock_eq_one_iff hirr (hE g.2)).mp h⟩
    · rintro ⟨-, hU⟩
      exact (planeBlock_eq_one_iff hirr (hE g.2)).mpr hU
  set R : Subgroup ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
    φ.range.map (toLinEquiv (Fin 2) K).toMonoidHom with hR
  have hRle : R ≤ TauCeti.QuadraticMap.orthogonalGroup (binaryForm K b c) := by
    intro f hf
    rw [hR] at hf
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hf
    obtain ⟨g, -, rfl⟩ := MonoidHom.mem_range.mp hA
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro p
    change binaryForm K b c ((toLinEquiv (Fin 2) K (φ g)) p) = binaryForm K b c p
    rw [toLinEquiv_apply, planeBlockGHom_apply]
    exact binaryForm_planeBlock_mulVec
      ((hE.trans (isoFix_le_lineStabilizer b c)) g.2) p
  have hRcard : Nat.card ↥R = Nat.card ↥φ.range := by
    rw [hR]
    exact Subgroup.card_map_of_injective (toLinEquiv (Fin 2) K).injective
  have hR2 : IsPGroup 2 ↥R := by
    rw [hR]
    have h1 : IsPGroup 2 ↥φ.range := by
      obtain ⟨n, hn⟩ := hE2.exists_card_eq
      exact IsPGroup.of_card_dvd_pow (n := n) (by rw [← hn]; exact Subgroup.card_range_dvd φ)
    exact IsPGroup.map (H := φ.range) h1 (toLinEquiv (Fin 2) K).toMonoidHom
  have hfinrank : Module.finrank K (Fin 2 → K) = 2 := Module.finrank_fin_fun K
  have hani : ∀ x : Fin 2 → K, x ≠ 0 → binaryForm K b c x ≠ 0 :=
    binaryForm_anisotropic hirr
  have hOcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (binaryForm K b c)) =
      2 * (Nat.card K + 1) :=
    CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_of_anisotropic
      (A := Fin 2 → K) (Q := binaryForm K b c) hfinrank hani
  have hRdvds : Nat.card ↥R ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (binaryForm K b c)) :=
    Subgroup.card_dvd_of_le hRle
  obtain ⟨m, -, hKcard⟩ := FiniteField.card K 2
  have hqeven : Even (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, hKcard, even_iff_two_dvd]
    exact dvd_pow_self 2 m.ne_zero
  have hqodd : Odd (Nat.card K + 1) := hqeven.add_one
  haveI hRfin : Finite ↥R :=
    Finite.of_injective (fun f : ↥R => fun p : Fin 2 → K =>
        (f.1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) p)
      (fun f g h => Subtype.ext (LinearEquiv.ext fun p => congrFun h p))
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hdvd : 2 ^ k ∣ 2 * (Nat.card K + 1) := by
    rw [← hk, ← hOcard]
    exact hRdvds
  have hle2 : 2 ^ k ≤ 2 := pow_two_le_two_of_dvd_two_mul_odd hqodd hdvd
  have hrange_le_two : Nat.card ↥φ.range ≤ 2 := by
    rw [← hRcard, hk]
    exact hle2
  have hkercard : Nat.card ↥φ.ker =
      Nat.card ↥(E ⊓ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := E ⊓ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) (K := E)
      inf_le_left).toEquiv
  calc
    Nat.card ↥E = Nat.card ↥φ.ker * Nat.card ↥φ.range :=
      (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card ↥(E ⊓ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) * 2 := by
      rw [hkercard]
      exact Nat.mul_le_mul_left _ hrange_le_two
    _ = 2 * Nat.card ↥(E ⊓ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K)) :=
      Nat.mul_comm _ _

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
