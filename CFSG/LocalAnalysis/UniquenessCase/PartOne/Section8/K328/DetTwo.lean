module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetDefs
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSL
import CFSG.LocalAnalysis.StandardType.GGSixTCLiftGroup
import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143Card
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpOrder
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSp
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
import CFSG.ClassicalInvolution.Asc77.AscSCH19
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinComm
import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverUni
import CFSG.LieType.SemisimpleCentralizers.OrderThree.Arith
import CFSG.Adapters.LieModelSmallOrders
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSL
public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagUnitary
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoOneLinear
import CFSG.LocalAnalysis.StandardType.TableC.POmegaBlockDeg
import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)

open CFSG.StandardType.ClassicalPosition CFSG.Assembly
open scoped commutatorElement

private lemma k328dpl2_blockKAction_blockK_pos
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K]  [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (_hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w)
    (_hinj : Function.Injective actK) :
    1 ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) := by
  have hne : LinearMap.range (Matrix.mulVecLin e) ≠ ⊥ := by
    intro hbot
    have hf : Matrix.mulVecLin e = 0 := LinearMap.range_eq_bot.mp hbot
    have h2 : e = 0 := by
      ext i j
      have h := congrFun (congrArg (fun g : (Fin (m + 1) → GaloisField 2 f) →ₗ[GaloisField 2 f]
          (Fin (m + 1) → GaloisField 2 f) => g (Pi.single j (1 : GaloisField 2 f))) hf) i
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h
    exact he.2.2.1 h2
  have : Module.Finite K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.Finite.of_restrictScalars_finite (GaloisField 2 f) K
      (LinearMap.range (Matrix.mulVecLin e))
  have : Nontrivial (LinearMap.range (Matrix.mulVecLin e)) :=
    Submodule.nontrivial_iff_ne_bot.mpr hne
  exact (Module.finrank_pos_iff_of_free (R := K)
    (M := LinearMap.range (Matrix.mulVecLin e))).mpr inferInstance

private lemma k328dpl2_blockKAction_det_one_range
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hcomp : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f))
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w) :
    ∀ g : LinearMap.range (Matrix.mulVecLin e) →ₗ[K] LinearMap.range (Matrix.mulVecLin e),
      LinearMap.det g = 1 → g ∈ Set.range actK := by
  exact fePSL_blockKAction_det_one_mem m f S hS he K π hcomp actK hact

private lemma k328dpl2_blockKAction_commutator_iso_group
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hcomp : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f))
    (hK : 4 ≤ Nat.card K ∨ 3 ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin e)))
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w)
    (hinj : Function.Injective actK) :
    Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup
        (Fin (Module.finrank K (LinearMap.range (Matrix.mulVecLin e)))) K) := by
  classical
  let W := LinearMap.range (Matrix.mulVecLin e)
  have hWfinite : Module.Finite K W :=
    Module.Finite.of_restrictScalars_finite (GaloisField 2 f) K W
  have hWfree : Module.Free K W := Module.Free.of_divisionRing K W
  let d := Module.finrank K W
  let b : Module.Basis (Fin d) K W := Module.finBasis K W
  let SLsub : Subgroup (Module.End K W)ˣ :=
    (LinearMap.det.comp (Units.coeHom (Module.End K W))).ker
  have hpos : 1 ≤ d :=
    k328dpl2_blockKAction_blockK_pos m f S he K actK hact hinj
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin d) K) := by
    by_cases hd : 2 ≤ d
    · rcases hK with hK4 | hd3
      · exact CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_perfect d K hd
          (Or.inr (by omega)) (Or.inr (by omega))
      · have hd3' : 3 ≤ d := by simpa only [d, W] using hd3
        exact CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_perfect d K hd
          (Or.inl (by omega)) (Or.inl (by omega))
    · have hd1 : d = 1 := by omega
      rw [hd1]
      infer_instance
  let eGL : (Module.End K W)ˣ ≃* Matrix.GeneralLinearGroup (Fin d) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  have hmapSL : SLsub.map eGL.toMonoidHom =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin d) K →* Kˣ).ker := by
    ext A
    rw [Subgroup.mem_map_equiv]
    change eGL.symm A ∈ (LinearMap.det.comp (Units.coeHom (Module.End K W))).ker ↔
      A ∈ (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin d) K →* Kˣ).ker
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.mem_ker,
      Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    change LinearMap.det (Matrix.toLin b b (A : Matrix (Fin d) (Fin d) K)) = 1 ↔
      (A : Matrix (Fin d) (Fin d) K).det = 1
    rw [LinearMap.det_toLin]
  let eSLsub : SLsub ≃* (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin d) K →* Kˣ).ker :=
    (SLsub.equivMapOfInjective eGL.toMonoidHom eGL.injective).trans
      (MulEquiv.subgroupCongr hmapSL)
  let eFinal : SLsub ≃* Matrix.SpecialLinearGroup (Fin d) K :=
    eSLsub.trans Matrix.SpecialLinearGroup.toGLKerEquiv.symm
  have hPerfSub : Group.IsPerfect SLsub :=
    Group.IsPerfect.ofSurjective (f := eFinal.symm.toMonoidHom) eFinal.symm.surjective
  let H := glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e
  let φ : H →* (Module.End K W)ˣ := actK.toHomUnits
  have hφinj : Function.Injective φ := by
    intro u v huv
    apply hinj
    have h : (φ u : Module.End K W) = (φ v : Module.End K W) :=
      congrArg (fun x : (Module.End K W)ˣ => (x : Module.End K W)) huv
    simpa only [φ, MonoidHom.coe_toHomUnits] using h
  have hSLsub_le_range : SLsub ≤ φ.range := by
    intro u hu
    have hdet : LinearMap.det (u : Module.End K W) = 1 := by
      simpa only [SLsub, MonoidHom.mem_ker,
        MonoidHom.comp_apply, Units.coeHom_apply] using hu
    obtain ⟨v, hv⟩ :=
      k328dpl2_blockKAction_det_one_range m f S hS he K π hcomp actK hact
        (u : Module.End K W) hdet
    refine MonoidHom.mem_range.mpr ⟨v, ?_⟩
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits]
    exact hv
  have hmapTop : (⊤ : Subgroup H).map H.subtype = H := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hmapSub : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).map H.subtype = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, hmapTop]
  have hmapPhi : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).map φ = SLsub := by
    apply le_antisymm
    · rw [Subgroup.map_commutator, Subgroup.map_top]
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hy
      have hmem : (((⁅u, v⁆ : H) : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f))) ∈ ⁅H, H⁆ := by
        rw [← hmapSub, Subgroup.mem_map]
        exact ⟨⁅u, v⁆,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v), rfl⟩
      have hdet := fePSL_blockKAction_commutator_det_one m f S he K actK hact
        (⁅u, v⁆ : H) hmem
      change LinearMap.det
        ((⁅φ u, φ v⁆ : (Module.End K W)ˣ) : Module.End K W) = 1
      rw [← map_commutatorElement φ u v]
      change LinearMap.det (actK (⁅u, v⁆ : H)) = 1
      exact hdet
    · rw [Subgroup.map_commutator, Subgroup.map_top]
      have hperf := Subgroup.commutator_eq_self (H := SLsub)
      rw [← hperf]
      exact Subgroup.commutator_mono hSLsub_le_range hSLsub_le_range
  let ePhi : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H) ≃* SLsub :=
    ((⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).equivMapOfInjective φ hφinj).trans
      (MulEquiv.subgroupCongr hmapPhi)
  let eH : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H) ≃*
      (⁅H, H⁆ : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1))
        (GaloisField 2 f))) :=
    ((⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).equivMapOfInjective H.subtype
      H.subtype_injective).trans (MulEquiv.subgroupCongr hmapSub)
  exact ⟨eH.symm.trans (ePhi.trans eFinal)⟩

private lemma k328dpl2_blockKAction_commutator_iso_basis
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hcomp : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f))
    (hK : 4 ≤ Nat.card K ∨ 3 ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin e)))
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w)
    (hinj : Function.Injective actK) :
    1 ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) ∧ Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup
        (Fin (Module.finrank K (LinearMap.range (Matrix.mulVecLin e)))) K) := by
  exact ⟨k328dpl2_blockKAction_blockK_pos m f S he K actK hact hinj,
    k328dpl2_blockKAction_commutator_iso_group m f S hS he K π hcomp hK actK hact hinj⟩

private lemma k328dpl2_blockKAction_commutator_iso
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Finite K] [Algebra (GaloisField 2 f) K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower (GaloisField 2 f) K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hcomp : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) (w : Fin (m + 1) → GaloisField 2 f))
    (hK : 4 ≤ Nat.card K ∨ 3 ≤ Module.finrank K (LinearMap.range (Matrix.mulVecLin e)))
    (actK : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e →*
      Module.End K (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (u : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e)
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actK u w : Fin (m + 1) → GaloisField 2 f) =
        Matrix.mulVec ((u : Matrix.SpecialLinearGroup (Fin (m + 1))
          (GaloisField 2 f)) : Matrix (Fin (m + 1)) (Fin (m + 1))
          (GaloisField 2 f)) w)
    (hinj : Function.Injective actK) :
    ∃ m' : ℕ, m' = Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) ∧ 1 ≤ m' ∧ Nonempty
      ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K) := by
  obtain ⟨h1, iso⟩ :=
    k328dpl2_blockKAction_commutator_iso_basis m f S hS he K π hcomp hK actK hact hinj
  exact ⟨Module.finrank K (LinearMap.range (Matrix.mulVecLin e)), rfl, h1, iso⟩

private lemma k328dpl2_blockGroup_rank_two
    (m f : ℕ) {S : Set (GL (Fin (m + 1)) (GaloisField 2 f))}
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    {K : Type} [Field K] {m' : ℕ}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (hiso : Nonempty ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
      Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K)) :
    2 ≤ m' := by
  by_contra h
  have hm' : m' ≤ 1 := by omega
  have : Subsingleton (Fin m') :=
    ⟨fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)⟩
  have : Subsingleton (Matrix.SpecialLinearGroup (Fin m') K) := inferInstance
  let H := ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
    glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆
  obtain ⟨φ⟩ := hiso
  have : Subsingleton H := ⟨fun a b => φ.injective (Subsingleton.elim (φ a) (φ b))⟩
  have : Nontrivial (J' ⧸ Subgroup.center J') := hJe.2.2.2.toNontrivial
  have : Nontrivial J' := (QuotientGroup.mk'_surjective (Subgroup.center J')).nontrivial
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial J')
  exact hxy (Subtype.ext (congrArg (fun z : H => (z :
      Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (Subsingleton.elim (⟨(x : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)),
      hJe.1 x.2⟩ : H) ⟨(y : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)),
      hJe.1 y.2⟩)))

private lemma k328dpl2_blockGroup_iso
    (m f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (hbig : 16 < Nat.card J') :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (m' : ℕ),
      2 ≤ m' ∧ (4 ≤ Nat.card K ∨ 3 ≤ m') ∧
      Nat.card K = 2 ^ (f * blockDegree
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e * m' ≤ m + 1 ∧
      Nonempty ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
        Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
        Matrix.SpecialLinearGroup (Fin m') K) := by
  classical
  obtain ⟨K, hKfield, hKalg, hKfin, π, hπsurj, hπker, hπdeg⟩ := exists_blockField hS hodd he
  let : Field K := hKfield
  let : Finite K := hKfin
  let W := LinearMap.range (Matrix.mulVecLin e)
  have hKcard : Nat.card K = 2 ^ (f * blockDegree
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) := fePSL_blockCard f _ hf hπdeg
  obtain ⟨hmod, htower, actK, hcomp, hact⟩ :=
    fePSL_blockKAction m f S hS he K π hπsurj hπker
  let : Module K W := hmod
  let : IsScalarTower (GaloisField 2 f) K W := htower
  have hWfinite : Module.Finite K W :=
    Module.Finite.of_restrictScalars_finite (GaloisField 2 f) K W
  have hinj : Function.Injective actK := fePSL_blockKAction_injective m f S he K actK hact
  have hK : 4 ≤ Nat.card K ∨ 3 ≤ Module.finrank K W := by
    by_cases h4 : 4 ≤ Nat.card K
    · exact Or.inl h4
    · refine Or.inr ?_
      by_contra h3
      have hle2 : Module.finrank K W ≤ 2 := by omega
      have hbd : 1 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e := by
        have h1 : 1 ≤ Module.finrank (GaloisField 2 f) K :=
          (Module.finrank_pos_iff_of_free (R := GaloisField 2 f) (M := K)).mpr inferInstance
        omega
      have hfd : 1 ≤ f * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have hK2 : Nat.card K = 2 := by
        have hlt : f * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2 := by
          by_contra hcon
          have h2 : 2 ≤ f * blockDegree
              (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e := by omega
          have h4' : 4 ≤ 2 ^ (f * blockDegree
              (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ (f * blockDegree
                  (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :=
                Nat.pow_le_pow_right (by norm_num) h2
          omega
        have h1' : f * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 1 :=
          by omega
        rw [hKcard, h1']; norm_num
      have hcardJ' : Nat.card J' ≤
          Nat.card (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :=
        Subgroup.card_le_of_le (hJe.1.trans (Subgroup.commutator_le_self _))
      have : Finite (Module.End K W) :=
        Finite.of_injective (fun g : Module.End K W => (g : W → W))
          (fun g h ghe => LinearMap.ext fun x => congrFun ghe x)
      have hcardAct : Nat.card (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) ≤
          Nat.card (Module.End K W) := Nat.card_le_card_of_injective actK hinj
      have hcardEnd : Nat.card (Module.End K W) =
          Nat.card K ^ (Module.finrank K W * Module.finrank K W) := by
        let b : Module.Basis (Fin (Module.finrank K W)) K W := Module.finBasis K W
        rw [Nat.card_congr (LinearMap.toMatrixAlgEquiv b).toEquiv]
        simp [Matrix, Nat.card_fun, ← pow_mul]
      have h16 : Nat.card J' ≤ 16 := by
        calc Nat.card J' ≤
              Nat.card (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) := hcardJ'
          _ ≤ Nat.card (Module.End K W) := hcardAct
          _ = 2 ^ (Module.finrank K W * Module.finrank K W) := by rw [hcardEnd, hK2]
          _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
          _ = 16 := by norm_num
      omega
  obtain ⟨m', hm'eq, hm'1, hiso⟩ :=
    k328dpl2_blockKAction_commutator_iso m f S hS he K π hcomp hK actK hact hinj
  have hm'2 : 2 ≤ m' := k328dpl2_blockGroup_rank_two m f hJe hiso
  have hdisj : 4 ≤ Nat.card K ∨ 3 ≤ m' := by
    rcases hK with h4 | h3
    · exact Or.inl h4
    · refine Or.inr ?_
      rw [hm'eq]
      simpa only [W] using h3
  have hdim : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e * m' ≤ m + 1 := by
    have htowerlaw : Module.finrank (GaloisField 2 f) K * Module.finrank K W =
        Module.finrank (GaloisField 2 f) W :=
      Module.finrank_mul_finrank (F := GaloisField 2 f) (K := K) (A := W)
    have hle : Module.finrank (GaloisField 2 f) W ≤ m + 1 := by
      have h := Submodule.finrank_le (R := GaloisField 2 f) W
      rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    calc blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e * m'
        = Module.finrank (GaloisField 2 f) K * Module.finrank K W := by rw [hπdeg, hm'eq]
      _ = Module.finrank (GaloisField 2 f) W := htowerlaw
      _ ≤ m + 1 := hle
  exact ⟨K, hKfield, hKfin, m', hm'2, hdisj, hKcard, hdim, hiso⟩

private def k328dpl2_slOrd (m q : ℕ) : ℕ :=
  q ^ (m * (m - 1) / 2) * ∏ j ∈ Finset.Icc 2 m, (q ^ j - 1)

private def k328dpl2_pslOrd (m q : ℕ) : ℕ :=
  k328dpl2_slOrd m q / Nat.gcd m (q - 1)

private lemma k328dpl2_odd_two_pow_sub_one (k : ℕ) (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h2 : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by norm_num)) h2 odd_one

private lemma k328dpl2_two_pow_dvd_pslOrd (m f d : ℕ) (hm : 2 ≤ m) (hf : 1 ≤ f)
    (hd : 1 ≤ d) :
    2 ^ (f * d * (m * (m - 1) / 2)) ∣ k328dpl2_pslOrd m (2 ^ (f * d)) := by
  set q := 2 ^ (f * d) with hq
  have hq1 : 1 ≤ f * d := by simpa using Nat.mul_le_mul hf hd
  rw [k328dpl2_pslOrd, k328dpl2_slOrd]
  set g := Nat.gcd m (q - 1) with hg
  have hgodd : Odd g := by
    rw [hg]
    exact Odd.of_dvd_nat (k328dpl2_odd_two_pow_sub_one (f*d) hq1)
      (by rw [hq]; exact Nat.gcd_dvd_right _ _)
  have hg_dvd : g ∣ q ^ (m * (m - 1) / 2) * ∏ j ∈ Finset.Icc 2 m, (q ^ j - 1) := by
    refine dvd_mul_of_dvd_right ?_ _
    refine (Nat.gcd_dvd_right m (q - 1)).trans ?_
    have hfac : q - 1 ∣ q ^ 2 - 1 := by
      have := Nat.pow_sub_one_dvd_pow_sub_one q (by norm_num : 1 ∣ 2)
      simpa using this
    exact hfac.trans (Finset.dvd_prod_of_mem _ (by simp [Finset.mem_Icc, hm]))
  have hcancel : (q ^ (m * (m - 1) / 2) * ∏ j ∈ Finset.Icc 2 m, (q ^ j - 1)) / g * g =
      q ^ (m * (m - 1) / 2) * ∏ j ∈ Finset.Icc 2 m, (q ^ j - 1) :=
    Nat.div_mul_cancel hg_dvd
  have hqT : q ^ (m * (m - 1) / 2) = 2 ^ (f * d * (m * (m - 1) / 2)) := by
    rw [hq, ← pow_mul]
  have hdvd : 2 ^ (f * d * (m * (m - 1) / 2)) ∣
      q ^ (m * (m - 1) / 2) * ∏ j ∈ Finset.Icc 2 m, (q ^ j - 1) := by
    rw [hqT]
    exact dvd_mul_right _ _
  have hcop : Nat.Coprime (2 ^ (f * d * (m * (m - 1) / 2))) g :=
    (Odd.coprime_two_left hgodd).pow_left _
  refine Nat.Coprime.dvd_of_dvd_mul_right hcop ?_
  rw [hcancel]
  exact hdvd

private lemma k328dpl2_card_sl (K : Type) [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (Matrix.SpecialLinearGroup (Fin m) K) = k328dpl2_slOrd m (Nat.card K) := by
  rw [k328dpl2_slOrd]
  exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hm

private lemma k328dpl2_card_psl (K : Type) [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin m) K) =
      k328dpl2_pslOrd m (Nat.card K) := by
  rw [k328dpl2_pslOrd, k328dpl2_slOrd]
  rw [Nat.card_congr
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m K).toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL hm]

private lemma k328dpl2_arith
    (m f d : ℕ) (hm : 2 ≤ m) (hf : 1 ≤ f) (hd : 1 ≤ d)
    (hpsl : k328dpl2_pslOrd m (2 ^ (f * d)) = 20160 ∨
            k328dpl2_pslOrd m (2 ^ (f * d)) = 5515776)
    (hsl : 60480 ≤ k328dpl2_slOrd m (2 ^ (f * d))) :
    m = 3 ∧ f * d = 2 := by
  have h2div := k328dpl2_two_pow_dvd_pslOrd m f d hm hf hd
  have h2not : ¬ 2 ^ 10 ∣ k328dpl2_pslOrd m (2 ^ (f * d)) := by
    rcases hpsl with h | h <;> rw [h] <;> decide
  have hb : f * d * (m * (m - 1) / 2) ≤ 9 := by
    by_contra hcon
    exact h2not (dvd_trans (pow_dvd_pow 2 (by omega)) h2div)
  have hfd1 : 1 ≤ f * d := by simpa using Nat.mul_le_mul hf hd
  have hm4 : m ≤ 4 := by
    by_contra hcon
    have h5 : 5 ≤ m := by omega
    have hT : 10 ≤ m * (m - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      simpa using Nat.mul_le_mul h5 (by omega : 4 ≤ m - 1)
    have : 10 ≤ f * d * (m * (m - 1) / 2) := by
      have := Nat.mul_le_mul hfd1 hT
      simpa using this
    omega
  set e := f * d with he
  have he1 : 1 ≤ e := by rw [he]; exact hfd1
  have key : (m = 3 ∧ e = 2) ∨ (m = 4 ∧ e = 1) := by
    interval_cases m <;> simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv] at hb
    · have hb2 : e ≤ 9 := by omega
      interval_cases e <;> exact absurd hpsl (by decide)
    · have hb3 : e ≤ 3 := by omega
      interval_cases e <;> first | exact absurd hpsl (by decide) | exact Or.inl ⟨rfl, rfl⟩
    · have hb4 : e = 1 := by omega
      rw [hb4]; exact Or.inr ⟨rfl, rfl⟩
  rcases key with ⟨rfl, he2⟩ | ⟨rfl, he1'⟩
  · exact ⟨rfl, he2⟩
  · exfalso
    rw [he1'] at hsl
    exact absurd hsl (by decide)

private theorem k328dpl2_isGLLift_toGL {m : ℕ} {K : Type} [Field K]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) K →*
      Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K)
    (z : Matrix.SpecialLinearGroup (Fin (m + 1)) K) :
    IsGLLift Matrix.SpecialLinearGroup.toGL ψ (Matrix.SpecialLinearGroup.toGL z) (ψ z⁻¹) := by
  intro u
  refine ⟨z * u * z⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv]
  · rw [map_mul, map_mul, map_inv]
    group

private theorem k328dpl2_isGLLift_zpow {m : ℕ} {K : Type} [Field K] [Finite K]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) K →*
      Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K}
    {s : GL (Fin (m + 1)) K} {b : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b) (i : ℤ) :
    IsGLLift Matrix.SpecialLinearGroup.toGL ψ (s ^ i) (b ^ i) := by
  obtain ⟨n, h | h⟩ := Int.eq_nat_or_neg i
  · subst h; simpa using hs.pow n
  · subst h
    simpa only [zpow_neg, zpow_natCast] using
      (hs.pow n).inv_of_injective Matrix.SpecialLinearGroup.toGL_injective

private lemma k328dpl2_lift {S : Type} [Group S] [Finite S] (m : ℕ) {K : Type} [Field K]
    [Finite K] (f : ℕ) (hf : 1 ≤ f) (hKcard : Nat.card K = 2 ^ f)
    (ePGL : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K)
    (hpos : K328DetPosIn S) :
    ∃ (Sset : Set (GL (Fin (m + 1)) K))
      (J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) K))
      (X' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K)),
      (∀ s ∈ Sset, ∀ s' ∈ Sset, Commute s s') ∧
      (∀ s ∈ Sset, Odd (orderOf s)) ∧
      CFSG.Assembly.IsComponentOf J' (Subgroup.comap Matrix.SpecialLinearGroup.toGL
        (Subgroup.centralizer Sset)) ∧
      Subgroup.map (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin (m + 1)) K))) J' = X' ∧
      CFSG.Open.IsQuasisimple ↥X' ∧
      X' ≠ ⊤ ∧
      60480 ≤ Nat.card X' ∧
      (Nat.card (X' ⧸ Subgroup.center X') = 20160 ∨
        Nat.card (X' ⧸ Subgroup.center X') = 5515776) := by
  classical
  obtain ⟨Z, X, hp, hXne⟩ := hpos
  have hp' : Pos (Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K)
      (Z.map ePGL.toMonoidHom) (X.map ePGL.toMonoidHom) := pos_map ePGL hp
  obtain ⟨hZcard, hZX, hXC, hsub, hqs, hcen, hlie⟩ := hp
  have hZ'card : Nat.card (Z.map ePGL.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective ePGL.injective, hZcard]
  have hcomp : CFSG.Assembly.IsComponentOf (X.map ePGL.toMonoidHom)
      (Subgroup.centralizer ((Z.map ePGL.toMonoidHom : Subgroup _) : Set _)) := by
    have hXC' : X.map ePGL.toMonoidHom ≤
        Subgroup.centralizer ((Z.map ePGL.toMonoidHom : Subgroup _) : Set _) := by
      rw [← map_centralizer_eq ePGL Z]
      exact Subgroup.map_mono hXC
    have hsub' : ((X.map ePGL.toMonoidHom).subgroupOf
        (Subgroup.centralizer ((Z.map ePGL.toMonoidHom : Subgroup _) : Set _))).IsSubnormal := by
      have h := isSubnormal_subgroupOf_map' ePGL hXC hsub
      rwa [map_centralizer_eq ePGL Z] at h
    refine ⟨hXC', ?_, ?_⟩
    · exact isSubnormal_iff_open.2 ((CFSG.Open.IsSubnormal.iff_subgroupOf hXC').2 hsub')
    · exact isQuasisimple_of_mulEquiv'
        (X.equivMapOfInjective ePGL.toMonoidHom ePGL.injective) hqs
  have hX'ne : X.map ePGL.toMonoidHom ≠ ⊤ := by
    intro htop
    have h : X.map ePGL.toMonoidHom = (⊤ : Subgroup S).map ePGL.toMonoidHom := by
      rw [htop, Subgroup.map_top_of_surjective _ ePGL.surjective]
    exact hXne (Subgroup.map_injective ePGL.injective h)
  let ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) K →*
      Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K))
  have hψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K) :=
    le_of_eq (QuotientGroup.ker_mk' _)
  obtain ⟨z', hz'mem, hz'ord, hz'gen⟩ :
      ∃ z' : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K,
        z' ∈ Z.map ePGL.toMonoidHom ∧ orderOf z' = 3 ∧
          Z.map ePGL.toMonoidHom = Subgroup.zpowers z' := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Z.map ePGL.toMonoidHom)) 3 (by rw [hZ'card])
    refine ⟨(w : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K), w.2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]; exact hw
    · symm
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]; exact w.2
      · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw, hZ'card]
  obtain ⟨z, hz⟩ : ∃ z : Matrix.SpecialLinearGroup (Fin (m + 1)) K, ψ z = z' :=
    QuotientGroup.mk'_surjective _ z'
  have hz'3 : z' ^ 3 = 1 := by rw [← hz'ord]; exact pow_orderOf_eq_one z'
  have hcenterOdd : Odd (Nat.card (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (m + 1)) K))) := by
    have hdvd : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) ∣
        Nat.card K - 1 := by
      rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
        (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))).toEquiv, ← Nat.card_units K]
      exact Subgroup.card_subgroup_dvd_card _
    exact Odd.of_dvd_nat (by rw [hKcard]; exact k328dpl2_odd_two_pow_sub_one f hf) hdvd
  have hzodd : Odd (orderOf z) := by
    have hz3ker : z ^ 3 ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hz, hz'3]
    have hz3 : z ^ 3 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K) := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K))]
      exact hz3ker
    have hz3ord : orderOf (z ^ 3) ∣
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) := by
      have := orderOf_dvd_natCard (⟨z ^ 3, hz3⟩ :
        Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K))
      simpa [Subgroup.orderOf_coe] using this
    have hzord : orderOf z ∣ Nat.card (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin (m + 1)) K)) * 3 := by
      rw [mul_comm (Nat.card (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin (m + 1)) K))) 3,
        orderOf_dvd_iff_pow_eq_one, pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp hz3ord
    exact Odd.of_dvd_nat (hcenterOdd.mul (by norm_num : Odd 3)) hzord
  let g : GL (Fin (m + 1)) K := Matrix.SpecialLinearGroup.toGL z⁻¹
  have hgz : orderOf g = orderOf z := by
    have h1 : g = (Matrix.SpecialLinearGroup.toGL z)⁻¹ := by
      rw [show g = Matrix.SpecialLinearGroup.toGL z⁻¹ from rfl, map_inv]
    rw [h1, orderOf_inv]
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, pow_orderOf_eq_one, map_one]
    · rw [orderOf_dvd_iff_pow_eq_one]
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [map_pow, map_one, pow_orderOf_eq_one]
  have hgodd : Odd (orderOf g) := by rw [hgz]; exact hzodd
  have hg_lift : IsGLLift Matrix.SpecialLinearGroup.toGL ψ g z' := by
    have h := k328dpl2_isGLLift_toGL ψ z⁻¹
    change IsGLLift Matrix.SpecialLinearGroup.toGL ψ
      (Matrix.SpecialLinearGroup.toGL z⁻¹) z'
    simpa [hz, map_inv] using h
  let Sset : Set (GL (Fin (m + 1)) K) := {s | s ∈ Subgroup.zpowers g ∧
      ∃ d ∈ Z.map ePGL.toMonoidHom, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d}
  have hS : ∀ s ∈ Sset, ∀ s' ∈ Sset, Commute s s' := by
    intro s hs s' hs'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs.1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs'.1
    exact ((Commute.refl g).zpow_left i).zpow_right j
  have hodd : ∀ s ∈ Sset, Odd (orderOf s) := by
    intro s hs
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs.1
    rw [orderOf_zpow]
    exact Odd.of_dvd_nat hgodd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  have hψrange : ψ.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have hJ : CFSG.Assembly.IsComponentOf (X.map ePGL.toMonoidHom)
      (ψ.range ⊓ Subgroup.centralizer
        ((Z.map ePGL.toMonoidHom : Subgroup _) : Set _)) := by
    rw [hψrange, top_inf_eq]; exact hcomp
  have hlift : ∀ d ∈ Z.map ePGL.toMonoidHom,
      ∃ s, s ∈ Subgroup.zpowers g ∧ IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d := by
    intro d hd
    rw [hz'gen] at hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact ⟨g ^ i, Subgroup.zpow_mem_zpowers g i, k328dpl2_isGLLift_zpow hg_lift i⟩
  obtain ⟨J', hJ', hJ'map⟩ := StepA.exists_isComponentOf_comap_lift_of_isGLLift
    Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective ψ hψ
    (fun s => s ∈ Subgroup.zpowers g) hJ hlift
  have hXge : 60480 ≤ Nat.card (X.map ePGL.toMonoidHom) := by
    rcases k328det_posCard (Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K) _ _ hp' with
      h | h <;> omega
  have hpsl : Nat.card ((X.map ePGL.toMonoidHom) ⧸
        Subgroup.center (X.map ePGL.toMonoidHom)) = 20160 ∨
      Nat.card ((X.map ePGL.toMonoidHom) ⧸
        Subgroup.center (X.map ePGL.toMonoidHom)) = 5515776 := by
    rcases hp'.2.2.2.2.2.2 with hl | hl
    · exact Or.inl (CFSG.Blueprint.LieModel.card_psl_three_four hl)
    · exact Or.inr (by
        rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num : 3 ≠ 0) hl]
        decide +kernel)
  have hXq : CFSG.Open.IsQuasisimple ↥(X.map ePGL.toMonoidHom) :=
    isQuasisimple_of_mulEquiv'
      (X.equivMapOfInjective ePGL.toMonoidHom ePGL.injective) hqs
  exact ⟨Sset, J', X.map ePGL.toMonoidHom, hS, hodd, hJ', hJ'map, hXq, hX'ne, hXge, hpsl⟩

private lemma k328dpl2_component_eq
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    {K : Type} [Field K] [Finite K] {m' : ℕ} (hm' : 2 ≤ m')
    (h22 : m' ≠ 2 ∨ Nat.card K ≠ 2) (h23 : m' ≠ 2 ∨ Nat.card K ≠ 3)
    (hiso : Nonempty ((⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :
      Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ≃*
      Matrix.SpecialLinearGroup (Fin m') K)) :
    J' = ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ := by
  let H := ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
    glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆
  obtain ⟨φ⟩ := hiso
  have hSLq : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m') K) :=
    ⟨(CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
        m' K hm' h22 h23).1.commutator_eq_top,
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
        m' K hm' h22 h23).2.1⟩
  have hHq : CFSG.Open.IsQuasisimple H := CFSG.Open.IsQuasisimple.of_mulEquiv φ hSLq
  have hsub : CFSG.Open.IsSubnormal (J'.subgroupOf H) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib (CFSG.Assembly.IsSubnormal.subgroupOf hJe.2.1)
  have : Group.IsPerfect J' := ⟨hJe.2.2.1⟩
  have : Group.IsPerfect (J'.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJe.1).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJe.1).symm.surjective
  rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
    hHq (J'.subgroupOf H) hsub with hbot | htop
  · exfalso
    have hJ'bot : J' = ⊥ := by
      have hdisj : Disjoint J' H := Subgroup.subgroupOf_eq_bot.mp hbot
      rwa [disjoint_iff, inf_eq_left.mpr hJe.1] at hdisj
    have hnt : Nontrivial J' := CFSG.ComponentClassification.Quasisimple.nontrivial hJe.2.2
    rw [hJ'bot] at hnt
    exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
  · exact le_antisymm hJe.1 (Subgroup.subgroupOf_eq_top.mp htop)

private lemma k328dpl2_component_iso
    (m f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    (hbig : 16 < Nat.card J') :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (m' : ℕ),
      2 ≤ m' ∧ (4 ≤ Nat.card K ∨ 3 ≤ m') ∧
      Nat.card K = 2 ^ (f * blockDegree
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e * m' ≤ m + 1 ∧
      Nonempty (J' ≃* Matrix.SpecialLinearGroup (Fin m') K) := by
  obtain ⟨K, hKfield, hKfin, m', hm'2, hdisj, hKcard, hdim, ⟨φ⟩⟩ :=
    k328dpl2_blockGroup_iso m f hf S hS hodd he hJe hbig
  have h22 : m' ≠ 2 ∨ Nat.card K ≠ 2 := by
    rcases hdisj with h4 | h3
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have h23 : m' ≠ 2 ∨ Nat.card K ≠ 3 := by
    rcases hdisj with h4 | h3
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hJeq : J' = ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :=
    k328dpl2_component_eq m f S hJe hm'2 h22 h23 ⟨φ⟩
  exact ⟨K, hKfield, hKfin, m', hm'2, hdisj, hKcard, hdim,
    ⟨(MulEquiv.subgroupCongr hJeq).trans φ⟩⟩

private lemma k328dpl2_center_quotient_card
    {G H : Type} [Group G] [Group H]
    (hG : CFSG.Open.IsQuasisimple G) (hH : CFSG.Open.IsQuasisimple H)
    (φ : G →* H) (hφ : Function.Surjective φ) :
    Nat.card (G ⧸ Subgroup.center G) = Nat.card (H ⧸ Subgroup.center H) := by
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hG.2
  have : IsSimpleGroup (H ⧸ Subgroup.center H) := hH.2
  have hcenter_le : Subgroup.center G ≤ (Subgroup.center H).comap φ := by
    intro z hz
    rw [Subgroup.mem_comap]
    exact Subgroup.map_center_le_center hφ (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
  let φbar : G ⧸ Subgroup.center G →* H ⧸ Subgroup.center H :=
    QuotientGroup.map (Subgroup.center G) (Subgroup.center H) φ hcenter_le
  have hφbar : Function.Surjective φbar := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) y
    obtain ⟨g, rfl⟩ := hφ x
    exact ⟨QuotientGroup.mk' _ g, by simp [φbar]⟩
  have hker : φbar.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top φbar.ker with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (H ⧸ Subgroup.center H) := ⟨fun a b => by
        obtain ⟨x, rfl⟩ := hφbar a
        obtain ⟨y, rfl⟩ := hφbar b
        have hx : φbar x = 1 := by
          have hxmem : x ∈ φbar.ker := by rw [h]; exact Subgroup.mem_top x
          simpa [MonoidHom.mem_ker] using hxmem
        have hy : φbar y = 1 := by
          have hymem : y ∈ φbar.ker := by rw [h]; exact Subgroup.mem_top y
          simpa [MonoidHom.mem_ker] using hymem
        rw [hx, hy]⟩
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (H ⧸ Subgroup.center H))
      exact hab (Subsingleton.elim a b)
  exact Nat.card_congr (MulEquiv.ofBijective φbar
    ⟨(MonoidHom.ker_eq_bot_iff φbar).mp hker, hφbar⟩).toEquiv

private lemma k328dpl2_order_transfer
    (m' : ℕ) (hm' : 1 ≤ m') {K : Type} [Field K] [Finite K]
    {J' X' : Type} [Group J'] [Group X']
    (hisoJ : J' ≃* Matrix.SpecialLinearGroup (Fin m') K)
    (hcardJX : Nat.card X' ≤ Nat.card J')
    (hZ : Nat.card (J' ⧸ Subgroup.center J') = Nat.card (X' ⧸ Subgroup.center X'))
    (hXge : 60480 ≤ Nat.card X')
    (hpsl : Nat.card (X' ⧸ Subgroup.center X') = 20160 ∨
            Nat.card (X' ⧸ Subgroup.center X') = 5515776) :
    60480 ≤ k328dpl2_slOrd m' (Nat.card K) ∧
      (k328dpl2_pslOrd m' (Nat.card K) = 20160 ∨
        k328dpl2_pslOrd m' (Nat.card K) = 5515776) := by
  constructor
  · rw [← k328dpl2_card_sl K hm']
    exact hXge.trans (hcardJX.trans (le_of_eq (Nat.card_congr hisoJ.toEquiv)))
  · have hPSL : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin m') K) =
        Nat.card (J' ⧸ Subgroup.center J') :=
      (Nat.card_congr (QuotientGroup.congr (Subgroup.center J')
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin m') K)) hisoJ
        (Subgroup.map_center_eq hisoJ)).toEquiv).symm
    rw [← k328dpl2_card_psl K hm', hPSL, hZ]
    exact hpsl

private lemma k328dpl2_block_arith
    (n' f : ℕ) (hf : 1 ≤ f) {S : Type} [Group S] [Finite S]
    (ePGL : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (n' + 1)) (GaloisField 2 f))
    (hpos : K328DetPosIn S)
    (hn : n' + 1 ≤ 4 ∨ ((n' + 1 = 5 ∨ n' + 1 = 6 ∨ n' + 1 = 7) ∧ 2 ^ f % 3 = 2)) :
    (n' + 1 = 4 ∧ f = 2) ∨ ((n' + 1 = 6 ∨ n' + 1 = 7) ∧ f = 1) := by
  obtain ⟨Sset, J', X', hScomm, hSodd, hJcomp, hJmap, hXq, hXne, hXge, hpsl⟩ :=
    k328dpl2_lift n' f hf (GaloisField.card 2 f (by omega)) ePGL hpos
  obtain ⟨e, he, hJe⟩ :=
    exists_isComponentOf_glBlockCentralizer_PSL n' (GaloisField 2 f) Sset hScomm hJcomp
  let ψ := QuotientGroup.mk' (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin (n' + 1)) (GaloisField 2 f)))
  have hJcard : Nat.card X' ≤ Nat.card J' := by
    have hsurj : Function.Surjective (fun x : J' => (⟨ψ x, by
        rw [← hJmap]; exact Subgroup.mem_map_of_mem ψ x.2⟩ : X')) := by
      intro y
      have hy : (y : Matrix.ProjectiveSpecialLinearGroup (Fin (n' + 1))
          (GaloisField 2 f)) ∈ J'.map ψ := by
        rw [hJmap]; exact y.2
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact Nat.card_le_card_of_surjective _ hsurj
  have hbig : 16 < Nat.card J' := by
    have : (16 : ℕ) < 60480 := by norm_num
    omega
  obtain ⟨K', hK'field, hK'fin, m', hm'2, hdisj, hK'card, hdim, ⟨φ⟩⟩ :=
    k328dpl2_component_iso n' f hf Sset hScomm hSodd he hJe hbig
  let : Field K' := hK'field
  let : Finite K' := hK'fin
  have h22 : m' ≠ 2 ∨ Nat.card K' ≠ 2 := by
    rcases hdisj with h4 | h3
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have h23 : m' ≠ 2 ∨ Nat.card K' ≠ 3 := by
    rcases hdisj with h4 | h3
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hJq : CFSG.Open.IsQuasisimple ↥J' :=
    CFSG.Open.IsQuasisimple.of_mulEquiv φ
      ⟨(CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
          m' K' hm'2 h22 h23).1.commutator_eq_top,
        (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
          m' K' hm'2 h22 h23).2.1⟩
  let φJX : ↥J' →* ↥X' :=
    (MulEquiv.subgroupCongr hJmap).toMonoidHom.comp (ψ.subgroupMap J')
  have hφJX : Function.Surjective φJX :=
    (MulEquiv.subgroupCongr hJmap).surjective.comp (MonoidHom.subgroupMap_surjective ψ J')
  have hZ := k328dpl2_center_quotient_card hJq hXq φJX hφJX
  have hm'1 : 1 ≤ m' := by omega
  obtain ⟨hsl, hpsl'⟩ := k328dpl2_order_transfer m' hm'1 φ hJcard hZ hXge hpsl
  set d := blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' Sset)) e with hd_def
  have hd1 : 1 ≤ d := by
    by_contra h
    have h0 : d = 0 := by omega
    have h1 : Nat.card K' = 1 := by rw [hK'card, h0, mul_zero, pow_zero]
    have h2 : 1 < Nat.card K' := Finite.one_lt_card
    omega
  have hsl' : 60480 ≤ k328dpl2_slOrd m' (2 ^ (f * d)) := by rw [← hK'card]; exact hsl
  have hpsl'' : k328dpl2_pslOrd m' (2 ^ (f * d)) = 20160 ∨
      k328dpl2_pslOrd m' (2 ^ (f * d)) = 5515776 := by rw [← hK'card]; exact hpsl'
  obtain ⟨hm'3, hfd⟩ := k328dpl2_arith m' f d hm'2 hf hd1 hpsl'' hsl'
  have hdim3 : 3 * d ≤ n' + 1 := by
    have := hdim
    rw [hm'3] at this
    simpa [mul_comm] using this
  have hd_le : d ≤ 2 := by
    have hdvd : d ∣ 2 := ⟨f, by rw [mul_comm]; exact hfd.symm⟩
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hd_cases : d = 1 ∨ d = 2 := by omega
  rcases hd_cases with hd1' | hd2'
  · rw [hd1'] at hfd hdim3
    have hf2 : f = 2 := by omega
    have h3 : 3 ≤ n' + 1 := by omega
    have hn4 : n' + 1 ≤ 4 := by
      rcases hn with h | ⟨-, hmod⟩
      · exact h
      · exfalso
        have : 2 ^ f % 3 = 1 := by rw [hf2]; norm_num
        omega
    have hne3 : n' + 1 ≠ 3 := by
      intro h3eq
      have hSle : Nat.card X' ≤ Nat.card S := by
        have h1 : Nat.card X' ≤ Nat.card (Matrix.ProjectiveSpecialLinearGroup
            (Fin (n' + 1)) (GaloisField 2 f)) :=
          Nat.card_le_card_of_injective (Subgroup.subtype X') (Subgroup.subtype_injective X')
        rwa [← Nat.card_congr ePGL.toEquiv] at h1
      have hScard : Nat.card S = k328dpl2_pslOrd (n' + 1) (2 ^ f) := by
        rw [Nat.card_congr ePGL.toEquiv,
          k328dpl2_card_psl (GaloisField 2 f) (m := n' + 1) (by omega),
          GaloisField.card 2 f (by omega)]
      have : Nat.card X' ≤ 20160 := by
        calc Nat.card X' ≤ Nat.card S := hSle
          _ = k328dpl2_pslOrd (n' + 1) (2 ^ f) := hScard
          _ = 20160 := by rw [h3eq, hf2]; decide +kernel
      omega
    have hn4' : n' + 1 = 4 := by omega
    exact Or.inl ⟨hn4', hf2⟩
  · rw [hd2'] at hfd hdim3
    have hf1 : f = 1 := by omega
    have h6 : 6 ≤ n' + 1 := by omega
    have hn67 : n' + 1 = 6 ∨ n' + 1 = 7 := by
      rcases hn with h | ⟨h, -⟩
      · omega
      · omega
    exact Or.inr ⟨hn67, hf1⟩

theorem k328det_famPSLTwo :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n f : ℕ,
      (n ≤ 4 ∨ ((n = 5 ∨ n = 6 ∨ n = 7) ∧ 2 ^ f % 3 = 2)) → LieModel S .PSL n 2 f → K328DetPosIn S →
        LieModel S .PSL 4 2 2 ∨ LieModel S .PSL 6 2 1 ∨ LieModel S .PSL 7 2 1 := by
  intro S _ _ hSsimple n f hn hmodel hpos
  have hadm := CFSG.Blueprint.LieModel.admissible hmodel
  have hf : 1 ≤ f := hadm.2.1
  have hn2 : 2 ≤ n := hadm.2.2.1
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hclass : CFSG.Open.StatedClassicalModel S .PSL (n' + 1) 2 f :=
    CFSG.Blueprint.LieModel.statedClassicalModel hmodel (by decide)
  have hclass2 := hclass
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨eS⟩⟩ := hclass2
  let : Field K := hKfield
  let : Finite K := hKfin
  let ePSL : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (n' + 1)) K :=
    eS.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      (n' + 1) K).symm
  let ePGL : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (n' + 1)) (GaloisField 2 f) :=
    ePSL.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 f (by omega) hKcard)
      (Fin (n' + 1)))
  rcases k328dpl2_block_arith n' f hf ePGL hpos hn with ⟨h4, hf2⟩ | ⟨h67, hf1⟩
  · rw [h4, hf2] at hclass
    exact Or.inl (Or.inl ⟨by decide, hclass⟩)
  · rcases h67 with h6 | h7
    · rw [h6, hf1] at hclass
      exact Or.inr (Or.inl (Or.inl ⟨by decide, hclass⟩))
    · rw [h7, hf1] at hclass
      exact Or.inr (Or.inr (Or.inl ⟨by decide, hclass⟩))
open CFSG.Open (StatedProj StatedSU StatedSL StatedScalars)

private theorem k328dpu2_heldSU_quot {a m : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ m) ^ 2) (ha : 2 ≤ a) (hm : 1 ≤ m)
    {τ' : E ≃+* E} (hτ' : ∀ x, τ' (τ' x) = x) (hτ'Q : ∀ x, τ' x = x ^ 2 ^ m) :
    Nonempty (CFSG.LieType.SemisimpleCentralizers.Held.heldSU a E τ' hτ' ⧸ Subgroup.center (CFSG.LieType.SemisimpleCentralizers.Held.heldSU a E τ' hτ') ≃*
      StatedProj (StatedSU a (2 ^ m) E)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdat : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m E := ⟨Nat.prime_two, hm, by rw [hE, ← pow_mul, Nat.mul_comm]⟩
  have : CharP E 2 := hdat.charP
  have hSUeq : CFSG.LieType.SemisimpleCentralizers.Held.heldSU a E τ' hτ' = StatedSU a (2 ^ m) E :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτ'Q
  have hcen : Subgroup.center (StatedSU a (2 ^ m) E) =
      (StatedScalars (Fin a) E).subgroupOf (StatedSU a (2 ^ m) E) := by
    rcases (show a = 2 ∨ 3 ≤ a by omega) with rfl | ha3
    · have h1 : Subgroup.center (StatedSU 2 (2 ^ m) E) = ⊥ :=
        CFSG.ComponentClassification.RankTwoClassical.center_statedSU_two_eq_bot (K := E) (f := m) hE
      have h2 : (StatedScalars (Fin 2) E).subgroupOf (StatedSU 2 (2 ^ m) E) ≤
          Subgroup.center (StatedSU 2 (2 ^ m) E) :=
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
      rw [h1] at h2 ⊢
      exact (le_bot_iff.mp h2).symm
    · exact CFSG.LieType.SemisimpleCentralizers.HeldLang.center_statedSU_eq hdat ha3
  refine ⟨?_⟩
  rw [hSUeq]
  exact QuotientGroup.quotientMulEquivOfEq hcen

private theorem k328dpu2_card_SU {a m : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ m) ^ 2) (hm : 1 ≤ m) (ha : 2 ≤ a) :
    Nat.card (StatedProj (StatedSU a (2 ^ m) E)) =
      (2 ^ m) ^ (a * (a - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 a, (((2 ^ m : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
          Nat.gcd a (2 ^ m + 1) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (p := 2) (f := m) Nat.prime_two hm hE ha]

private theorem k328dpu2_card_SL {c k : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 2 ^ k) (hc : 1 ≤ c) :
    Nat.card (StatedProj (StatedSL c E)) =
      (2 ^ k) ^ (c * (c - 1) / 2) *
        (∏ j ∈ Finset.Icc 2 c, ((2 ^ k) ^ j - 1)) / Nat.gcd c (2 ^ k - 1) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := c) hc, hE]

private theorem k328dpu2_arith_u {a m N : ℕ} {E : Type} [Field E] [Finite E] (ha : 2 ≤ a)
    (hE : Nat.card E = (2 ^ m) ^ 2) (hN : N = 20160 ∨ N = 5515776)
    (hc : Nat.card (StatedProj (StatedSU a (2 ^ m) E)) = N) : a = 3 ∧ m = 3 := by
  have hm : 1 ≤ m := by
    by_contra h
    push Not at h
    have h1 : Nat.card E = 1 := by rw [hE]; norm_num at h ⊢; omega
    have := Finite.one_lt_card (α := E)
    omega
  have hp := CFSG.LieType.SemisimpleCentralizers.HeldLang.padicValNat_card_psu
    (K := E) (a := m) (d := a) hm (by omega) hE
  rw [hc] at hp
  have hval : m * (a * (a - 1) / 2) = 6 ∨ m * (a * (a - 1) / 2) = 9 := by
    rcases hN with rfl | rfl
    · left
      have : padicValNat 2 20160 = 6 := by decide +kernel
      rw [this] at hp
      exact hp.symm
    · right
      have : padicValNat 2 5515776 = 9 := by decide +kernel
      rw [this] at hp
      exact hp.symm
  have ha4 : a ≤ 4 := by
    by_contra h
    push Not at h
    have ha5 : 5 ≤ a := by omega
    have ha4' : 4 ≤ a - 1 := by omega
    have h2 : 10 ≤ a * (a - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have := Nat.mul_le_mul ha5 ha4'
      omega
    have h3 : 1 * 10 ≤ m * (a * (a - 1) / 2) := Nat.mul_le_mul hm h2
    rcases hval with h | h <;> omega
  interval_cases a
  · rcases hval with h | h
    · have hm6 : m = 6 := by omega
      subst hm6
      have hcard : Nat.card (StatedProj (StatedSU 2 (2 ^ 6) E)) = 262080 := by
        rw [k328dpu2_card_SU (m := 6) (a := 2) hE (by norm_num) (by norm_num)]
        decide +kernel
      rw [hcard] at hc
      rcases hN with hN | hN <;> omega
    · have hm9 : m = 9 := by omega
      subst hm9
      have hcard : Nat.card (StatedProj (StatedSU 2 (2 ^ 9) E)) = 134217216 := by
        rw [k328dpu2_card_SU (m := 9) (a := 2) hE (by norm_num) (by norm_num)]
        decide +kernel
      rw [hcard] at hc
      rcases hN with hN | hN <;> omega
  · rcases hval with h | h
    · have hm2 : m = 2 := by omega
      subst hm2
      have hcard : Nat.card (StatedProj (StatedSU 3 (2 ^ 2) E)) = 62400 := by
        rw [k328dpu2_card_SU (m := 2) (a := 3) hE (by norm_num) (by norm_num)]
        decide +kernel
      rw [hcard] at hc
      rcases hN with hN | hN <;> omega
    · have hm3 : m = 3 := by omega
      exact ⟨rfl, hm3⟩
  · rcases hval with h | h
    · have hm1 : m = 1 := by omega
      subst hm1
      have hcard : Nat.card (StatedProj (StatedSU 4 (2 ^ 1) E)) = 25920 := by
        rw [k328dpu2_card_SU (m := 1) (a := 4) hE (by norm_num) (by norm_num)]
        decide +kernel
      rw [hcard] at hc
      rcases hN with hN | hN <;> omega
    · omega

private theorem k328dpu2_arith_l {c k N : ℕ} {E : Type} [Field E] [Finite E] (hc2 : 2 ≤ c)
    (hk : Even k) (hE : Nat.card E = 2 ^ k) (hN : N = 20160 ∨ N = 5515776)
    (hcard : Nat.card (StatedProj (StatedSL c E)) = N) : c = 3 ∧ k = 2 := by
  have hk1 : 1 ≤ k := by
    by_contra h
    push Not at h
    have h1 : Nat.card E = 1 := by rw [hE]; norm_num at h ⊢; omega
    have := Finite.one_lt_card (α := E)
    omega
  have hp := CFSG.LieType.SemisimpleCentralizers.OrderThree.padicValNat_card_statedProj_statedSL
    (K := E) (p := 2) (m := k) (a := c) Nat.prime_two hk1 hE (by omega)
  rw [hcard] at hp
  have hval9 : ¬ k * (c * (c - 1) / 2) = 9 := by
    intro h
    have h2 : Even (k * (c * (c - 1) / 2)) := hk.mul_right _
    rw [h] at h2
    norm_num at h2
  have hval : k * (c * (c - 1) / 2) = 6 := by
    rcases hN with rfl | rfl
    · have : padicValNat 2 20160 = 6 := by decide +kernel
      rw [this] at hp
      exact hp.symm
    · have : padicValNat 2 5515776 = 9 := by decide +kernel
      rw [this] at hp
      exact absurd hp.symm hval9
  have hc4 : c ≤ 4 := by
    by_contra h
    push Not at h
    have hc5 : 5 ≤ c := by omega
    have hc4' : 4 ≤ c - 1 := by omega
    have h1 : 10 ≤ c * (c - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have := Nat.mul_le_mul hc5 hc4'
      omega
    have h2 : 1 * 10 ≤ k * (c * (c - 1) / 2) := Nat.mul_le_mul hk1 h1
    omega
  interval_cases c
  · have hk6 : k = 6 := by omega
    subst hk6
    have hcard2 : Nat.card (StatedProj (StatedSL 2 E)) = 262080 := by
      rw [k328dpu2_card_SL (k := 6) (c := 2) hE (by norm_num)]
      decide +kernel
    rw [hcard2] at hcard
    rcases hN with hN | hN <;> omega
  · have hk2 : k = 2 := by omega
    exact ⟨rfl, hk2⟩
  · have hk1' : k = 1 := by omega
    subst hk1'
    norm_num at hk

private theorem k328dpu2_reduce {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (z : StatedProj (StatedSU n (2 ^ f) K)) (hz3 : z ^ 3 = 1)
    {X : Subgroup (StatedProj (StatedSU n (2 ^ f) K))}
    (hX : CFSG.Open.IsComponentOf X
      (Subgroup.centralizer ({z} : Set (StatedProj (StatedSU n (2 ^ f) K))))) :
    ∃ (zhat : ↥(StatedSU n (2 ^ f) K)) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x)
      (_hτQ : ∀ x, τ x = x ^ 2 ^ f) (J : Subgroup (GL (Fin n) K))
      (_ : (↥X ⧸ Subgroup.center ↥X) ≃* (↥J ⧸ Subgroup.center ↥J)),
      (↑zhat : GL (Fin n) K) ∈ CFSG.LieType.SemisimpleCentralizers.Held.heldGU n K τ hτ ∧
      (orderOf (↑zhat : GL (Fin n) K) : K) ≠ 0 ∧
      CFSG.Open.IsComponentOf J
        (Subgroup.centralizer ({(↑zhat : GL (Fin n) K)} : Set (GL (Fin n) K)) ⊓
          CFSG.LieType.SemisimpleCentralizers.Held.heldGU n K τ hτ) := by
  classical
  let M : Subgroup (GL (Fin n) K) := StatedSU n (2 ^ f) K
  let π : ↥M →* StatedProj M := QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf M)
  have hπapply (x : ↥M) : π x = QuotientGroup.mk x := rfl
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker ≤ Subgroup.center ↥M := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center M
  let zhat : ↥M := Classical.choose (hπsurj z)
  have hzhat : π zhat = z := Classical.choose_spec (hπsurj z)
  obtain ⟨τ, hτQ, hτ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv (K := K) (n := f) hK
  have hSU : CFSG.LieType.SemisimpleCentralizers.Held.heldSU n K τ hτ = M :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ
  let cj : MulAut ↥M := MulAut.conj zhat
  have hcj (x : ↥M) : cj x = zhat * x * zhat⁻¹ := MulAut.conj_apply zhat x
  have hfixβ : ∀ x : ↥M, π x ∈ Subgroup.centralizer ({z} : Set (StatedProj M)) →
      cj x * x⁻¹ ∈ Subgroup.center ↥M := by
    intro x hx
    apply hπker
    rw [MonoidHom.mem_ker]
    have hc : z * π x = π x * z := (Subgroup.mem_centralizer_iff.mp hx) z rfl
    rw [map_mul, map_inv, hcj, map_mul, map_mul, map_inv, hzhat, hc]
    group
  have hcomm : ∀ x y : ↥M, π x ∈ Subgroup.centralizer ({z} : Set (StatedProj M)) →
      π y ∈ Subgroup.centralizer ({z} : Set (StatedProj M)) → cj ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y hx hy
    have hz1 := hfixβ x hx
    have hz2 := hfixβ y hy
    have ex : cj x = (cj x * x⁻¹) * x := by group
    have ey : cj y = (cj y * y⁻¹) * y := by group
    rw [map_commutatorElement, ex, ey]
    exact CFSG.LocalAnalysis.GLTheoremA.HSubT.commutatorElement_central_mul hz1 hz2
  let Xpre : Subgroup ↥M := (Subgroup.centralizer ({z} : Set (StatedProj M))).comap π
  let Lh : Subgroup ↥M := X.comap π
  let P : Subgroup ↥M := ⁅Lh, Lh⁆
  let Csub : Subgroup ↥M := Subgroup.centralizer ({zhat} : Set ↥M)
  have hLh_sub : CFSG.Open.IsSubnormal Lh Xpre :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.isSubnormal_comap_open π hX.2.1
  have hPsub_X : CFSG.Open.IsSubnormal P Xpre :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.isSubnormal_commutator_open hLh_sub
  have hP_le_C : P ≤ Csub := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have h' := congrArg (fun t => t * zhat) (hcomm x y (hX.1 hx) (hX.1 hy))
    simpa [hcj, mul_assoc] using h'
  have hC_le_X : Csub ≤ Xpre := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have h := (Subgroup.mem_centralizer_iff.mp hx) zhat rfl
    have h' := congrArg π h
    simpa [map_mul, hzhat] using h'
  have hPsub_C : CFSG.Open.IsSubnormal P Csub := by
    have h := hPsub_X.inf_of_le hC_le_X
    rwa [inf_eq_left.mpr hP_le_C] at h
  have hLperf : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.mp ⟨hX.2.2.1⟩
  have hPmap : P.map π = X := by
    have hLh_map : Lh.map π = X := Subgroup.map_comap_eq_self_of_surjective hπsurj X
    show Subgroup.map π ⁅Lh, Lh⁆ = X
    rw [Subgroup.map_commutator, hLh_map, hLperf]
  have hPsurj : ∀ l ∈ X, ∃ p ∈ P, π p = l := by
    intro l hl
    have hl' : l ∈ P.map π := by rw [hPmap]; exact hl
    exact Subgroup.mem_map.mp hl'
  have hPdecomp : ∀ x ∈ Lh, ∃ w ∈ Subgroup.center ↥M, ∃ p ∈ P, x = w * p := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hPsurj (π x) hx
    refine ⟨x * p⁻¹, hπker ?_, p, hp, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, mul_inv_cancel]
  have hPperf : ⁅P, P⁆ = P := by
    apply le_antisymm
    · exact CFSG.LocalAnalysis.GLTheoremA.HSubT.commutator_self_le P
    · show ⁅Lh, Lh⁆ ≤ ⁅P, P⁆
      refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      obtain ⟨w₁, hw₁, p, hp, rfl⟩ := hPdecomp x hx
      obtain ⟨w₂, hw₂, q, hq, rfl⟩ := hPdecomp y hy
      rw [CFSG.LocalAnalysis.GLTheoremA.HSubT.commutatorElement_central_mul hw₁ hw₂]
      exact Subgroup.commutator_mem_commutator hp hq
  have hPLh : P ≤ Lh := CFSG.LocalAnalysis.GLTheoremA.HSubT.commutator_self_le Lh
  let πP : ↥P →* ↥X := MonoidHom.codRestrict (π.comp P.subtype) X (fun p => hPLh p.2)
  have hπsurjP : Function.Surjective πP := by
    intro l
    obtain ⟨p, hp, hpl⟩ := hPsurj l.1 l.2
    exact ⟨⟨p, hp⟩, Subtype.ext hpl⟩
  have hπkerP : πP.ker ≤ Subgroup.center ↥P := by
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    have hp' : π (p : ↥M) = 1 := congrArg Subtype.val hp
    have hz : (p : ↥M) ∈ Subgroup.center ↥M := hπker (MonoidHom.mem_ker.mpr hp')
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hz g
  have hpf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hPperf
  obtain ⟨eQ⟩ := CFSG.LieType.SemisimpleCentralizers.OrderThree.nonempty_quotientCenter_mulEquiv_of_surjective
    hpf πP hπsurjP hπkerP
  have : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := hX.2.2.2
  have hPQ : CFSG.Open.IsQuasisimple ↥P := ⟨hpf.commutator_eq_top, MulEquiv.isSimpleGroup eQ⟩
  have hPcomp : CFSG.Open.IsComponentOf P Csub := ⟨hP_le_C, hPsub_C, hPQ⟩
  let ι : ↥M →* GL (Fin n) K := M.subtype
  have hι : Function.Injective ι := Subtype.val_injective
  have hCeq : Csub =
      (Subgroup.centralizer ({(zhat : GL (Fin n) K)} : Set (GL (Fin n) K))).subgroupOf M := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simpa using congrArg Subtype.val (hx zhat rfl)
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subtype.ext (by simpa using hx (zhat : GL (Fin n) K) rfl)
  have hCmap : Csub.map ι = Subgroup.centralizer ({(zhat : GL (Fin n) K)} : Set (GL (Fin n) K)) ⊓ M := by
    rw [hCeq]
    exact Subgroup.subgroupOf_map_subtype _ _
  have hJcomp : CFSG.Open.IsComponentOf (P.map ι)
      (Subgroup.centralizer ({(zhat : GL (Fin n) K)} : Set (GL (Fin n) K)) ⊓ M) := by
    rw [← hCmap]
    exact CFSG.LocalAnalysis.GLTheoremA.HSubT.isComponentOf_map_of_injective ι hι hPcomp
  have hJSU : CFSG.Open.IsComponentOf (P.map ι)
      (Subgroup.centralizer ({(zhat : GL (Fin n) K)} : Set (GL (Fin n) K)) ⊓ CFSG.LieType.SemisimpleCentralizers.Held.heldSU n K τ hτ) := by
    rw [hSU]
    exact hJcomp
  have hJGU : CFSG.Open.IsComponentOf (P.map ι)
      (Subgroup.centralizer ({(zhat : GL (Fin n) K)} : Set (GL (Fin n) K)) ⊓ CFSG.LieType.SemisimpleCentralizers.Held.heldGU n K τ hτ) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isComponentOf_centralizer_gu_of_su hτ
      (zhat : GL (Fin n) K) hJSU
  have hs : (↑zhat : GL (Fin n) K) ∈ CFSG.LieType.SemisimpleCentralizers.Held.heldGU n K τ hτ := by
    have hmem : (↑zhat : GL (Fin n) K) ∈ CFSG.LieType.SemisimpleCentralizers.Held.heldSU n K τ hτ := by rw [hSU]; exact zhat.2
    exact (Subgroup.mem_inf.mp hmem).1
  have hord : (orderOf (↑zhat : GL (Fin n) K) : K) ≠ 0 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype K := Fintype.ofFinite K
    have hchar : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
    have h3mem : zhat ^ 3 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hzhat, hz3]
    rw [QuotientGroup.ker_mk'] at h3mem
    let N := (StatedScalars (Fin n) K).subgroupOf M
    have hoddN : Odd (Nat.card N) :=
      CFSG.LieType.SemisimpleCentralizers.HeldLang.odd_card_subgroupOf_scalars (K := K) (q := 2 ^ f)
        (d := n) hK (Even.pow_of_ne_zero (by norm_num) (by omega)) (pow_ne_zero _ two_ne_zero) M
    have hpow : zhat ^ (3 * Nat.card N) = 1 := by
      have hh : ((zhat ^ 3 : ↥M) ^ Nat.card N) = 1 := by
        have h := congrArg (fun y : N => (y : ↥M)) (pow_card_eq_one' (x := (⟨zhat ^ 3, h3mem⟩ : N)))
        simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
      rwa [pow_mul]
    have hdvd : orderOf zhat ∣ 3 * Nat.card N := orderOf_dvd_of_pow_eq_one hpow
    have hodd : Odd (orderOf zhat) :=
      Odd.of_dvd_nat ((show Odd 3 from ⟨1, by norm_num⟩).mul hoddN) hdvd
    have hcoeeq : orderOf (↑zhat : GL (Fin n) K) = orderOf zhat := Subgroup.orderOf_coe zhat
    intro h0
    have h2dvd : 2 ∣ orderOf (↑zhat : GL (Fin n) K) :=
      (CharP.cast_eq_zero_iff K 2 (orderOf (↑zhat : GL (Fin n) K))).mp h0
    rw [hcoeeq] at h2dvd
    exact hodd.not_two_dvd_nat h2dvd
  have eP : ↥P ≃* ↥(P.map ι) := Subgroup.equivMapOfInjective P ι hι
  have ePP' : (↥P ⧸ Subgroup.center ↥P) ≃* (↥(P.map ι) ⧸ Subgroup.center ↥(P.map ι)) :=
    QuotientGroup.congr (Subgroup.center ↥P) (Subgroup.center ↥(P.map ι)) eP
      (Subgroup.map_center_eq eP)
  refine ⟨zhat, τ, hτ, hτQ, P.map ι, eQ.symm.trans ePP', hs, hord, hJGU⟩

private theorem k328dpu2_classify {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (z : StatedProj (StatedSU n (2 ^ f) K)) (hz3 : z ^ 3 = 1)
    {X : Subgroup (StatedProj (StatedSU n (2 ^ f) K))}
    (hX : CFSG.Open.IsComponentOf X
      (Subgroup.centralizer ({z} : Set (StatedProj (StatedSU n (2 ^ f) K))))) :
    (∃ (a m : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧
        Nat.card E = (2 ^ (f * m)) ^ 2 ∧
        Nonempty (↥X ⧸ Subgroup.center ↥X ≃* StatedProj (StatedSU a (2 ^ (f * m)) E))) ∨
    (∃ (c e : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ c ∧
        Nat.card E = 2 ^ (f * (2 * e)) ∧
        Nonempty (↥X ⧸ Subgroup.center ↥X ≃* StatedProj (StatedSL c E))) := by
  classical
  obtain ⟨zhat, τ, hτ, hτQ, J, eXJ, hs, hord, hJGU⟩ := k328dpu2_reduce hK hf z hz3 hX
  rcases @CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.held_unitary_components_gu_sized
      CFSG.LieType.SemisimpleCentralizers.Held.SUComponentsTrivial_holds
      CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds
      (2 ^ f) n K _ _ τ hτ hτQ hK zhat hs hord J hJGU with
    ⟨a, dd, E, hEf, hEfin, τ', hτ', ha, hτ'dd, hcardE, ⟨eJ⟩⟩ |
    ⟨c, e, E, hEf, hEfin, hc, hcardE, ⟨eJ⟩⟩
  · let : Field E := hEf
    let : Finite E := hEfin
    have hE' : Nat.card E = (2 ^ (f * dd)) ^ 2 := by
      rw [hcardE]
      congr 1
      rw [← pow_mul]
    have hm' : 1 ≤ f * dd := by
      by_contra h
      push Not at h
      have h0 : f * dd = 0 := by omega
      have h1 : Nat.card E = 1 := by rw [hE', h0]; norm_num
      have := Finite.one_lt_card (α := E)
      omega
    have hτ'Q : ∀ x, τ' x = x ^ 2 ^ (f * dd) := by
      intro x
      rw [hτ'dd x, ← pow_mul]
    obtain ⟨eB⟩ := k328dpu2_heldSU_quot (a := a) (m := f * dd) (E := E) hE' ha hm' hτ' hτ'Q
    exact Or.inl ⟨a, dd, E, hEf, hEfin, ha, hE', ⟨eXJ.trans (eJ.trans eB)⟩⟩
  · let : Field E := hEf
    let : Finite E := hEfin
    have hE' : Nat.card E = 2 ^ (f * (2 * e)) := by rw [hcardE, ← pow_mul]
    exact Or.inr ⟨c, e, E, hEf, hEfin, hc, hE', ⟨eXJ.trans eJ⟩⟩

theorem k328det_famPSUTwo :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n f : ℕ,
      (n ≤ 4 ∨ ((n = 5 ∨ n = 6 ∨ n = 7) ∧ 2 ^ f % 3 = 1)) → LieModel S .PSU n 2 f → K328DetPosIn S →
        LieModel S .PSU 4 2 3 := by

  intro S _ _ hSsimp n f hn hLie hPos
  have hLieKeep : LieModel S .PSU n 2 f := hLie
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨eS⟩⟩ := hLie.statedClassicalModel (by decide)
  let : Field K := hKfield
  let : Finite K := hKfin
  have hf : 1 ≤ f := hadm.2.1
  have hPosKeep : K328DetPosIn S := hPos
  obtain ⟨Z0, X0, hpos0, hX0ne⟩ := hPos
  set Z : Subgroup (StatedProj (StatedSU n (2 ^ f) K)) := Z0.map eS.toMonoidHom
  set X : Subgroup (StatedProj (StatedSU n (2 ^ f) K)) := X0.map eS.toMonoidHom
  have hpos : Pos (StatedProj (StatedSU n (2 ^ f) K)) Z X := pos_map eS hpos0
  have hXcard : Nat.card X = 60480 ∨ Nat.card X = 16547328 := k328det_posCard _ Z X hpos
  obtain ⟨hZcard, hZX, hXC, hsub, hqs, hcen, hlie⟩ := hpos
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hborder⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZcard])
  have hb3 : orderOf (b : StatedProj (StatedSU n (2 ^ f) K)) = 3 := by
    rw [Subgroup.orderOf_coe, hborder]
  have hZgen : Z = Subgroup.zpowers (b : StatedProj (StatedSU n (2 ^ f) K)) := by
    have hle : Subgroup.zpowers (b : StatedProj (StatedSU n (2 ^ f) K)) ≤ Z :=
      Subgroup.zpowers_le.mpr b.2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hb3, hZcard])).symm
  let z : StatedProj (StatedSU n (2 ^ f) K) := (b : StatedProj (StatedSU n (2 ^ f) K))
  have hz3 : z ^ 3 = 1 := by
    show (b : StatedProj (StatedSU n (2 ^ f) K)) ^ 3 = 1
    rw [← hb3]
    exact pow_orderOf_eq_one _
  have hcent_eq : Subgroup.centralizer (Z : Set (StatedProj (StatedSU n (2 ^ f) K))) =
      Subgroup.centralizer ({z} : Set (StatedProj (StatedSU n (2 ^ f) K))) := by
    rw [hZgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hXopen : CFSG.Open.IsComponentOf X
      (Subgroup.centralizer ({z} : Set (StatedProj (StatedSU n (2 ^ f) K)))) := by
    rw [← hcent_eq]
    exact ⟨hXC, (CFSG.Open.IsSubnormal.iff_subgroupOf hXC).mpr hsub, hqs⟩
  let N : ℕ := Nat.card (↥X ⧸ Subgroup.center ↥X)
  have hXcardN : Nat.card X = N * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X), hcen]
  have hN : N = 20160 ∨ N = 5515776 := by
    rcases hXcard with h | h <;> rw [h] at hXcardN <;> omega
  have hf13 : f = 1 ∨ f = 3 := by
    rcases k328dpu2_classify hKcard hf z hz3 hXopen with
      ⟨a, m, E, hEf, hEfin, ha, hEcard, ⟨eXU⟩⟩ | ⟨c, e, E, hEf, hEfin, hc, hEcard, ⟨eXL⟩⟩
    · let : Field E := hEf
      let : Finite E := hEfin
      have hc' : Nat.card (StatedProj (StatedSU a (2 ^ (f * m)) E)) = N :=
        (Nat.card_congr eXU.toEquiv).symm
      obtain ⟨-, hfm⟩ := k328dpu2_arith_u (m := f * m) ha hEcard hN hc'
      exact (Nat.dvd_prime Nat.prime_three).mp ⟨m, hfm.symm⟩
    · let : Field E := hEf
      let : Finite E := hEfin
      have hc' : Nat.card (StatedProj (StatedSL c E)) = N :=
        (Nat.card_congr eXL.toEquiv).symm
      obtain ⟨-, hfe⟩ := k328dpu2_arith_l (k := f * (2 * e)) hc
        (⟨f * e, by ring⟩ : Even (f * (2 * e))) hEcard hN hc'
      have hf_dvd : f ∣ 2 := ⟨2 * e, hfe.symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hf_dvd with h | h
      · exact Or.inl h
      · exfalso
        subst h
        omega
  have hfmod : 2 ^ f % 3 = 2 := by rcases hf13 with rfl | rfl <;> decide
  have hnle : n ≤ 4 := by
    rcases hn with h | ⟨-, hc⟩
    · exact h
    · exfalso
      rw [hfmod] at hc
      norm_num at hc
  have hn34 : n = 3 ∨ n = 4 := by
    have := hadm.2.2.1
    omega
  rcases hn34 with rfl | rfl
  · rcases hf13 with rfl | rfl
    · exfalso
      exact hadm.2.2.2 (by decide)
    · exfalso
      have hS : Nat.card S = 5515776 := by
        rw [hLieKeep.card_eq_lieOrd (by norm_num)]
        decide +kernel
      exact absurd hPosKeep (k328det_not_posIn_of_card (by rw [hS]; decide) (by rw [hS]; decide))
  · rcases hf13 with rfl | rfl
    · exfalso
      have hS : Nat.card S = 25920 := by
        rw [hLieKeep.card_eq_lieOrd (by norm_num)]
        decide +kernel
      exact absurd hPosKeep (k328det_not_posIn_of_card (by rw [hS]; decide) (by rw [hS]; decide))
    · exact hLieKeep

open CFSG.Open (StatedSp StatedSL StatedSU StatedScalars StatedProj StatedClassicalModel)
open CFSG.ClassicalGroups.Symplectic
open CFSG.StandardType.ClassicalBlocks (GUFull)

private theorem k328dps2_charP {K : Type} [Field K] [Finite K] {f : ℕ}
    (h : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by simpa [Nat.card_eq_fintype_card] using h)

private theorem k328dps2_scalars_bot {n : ℕ} {K : Type} [Field K] [CharP K 2] (hn : 1 ≤ n) :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥ := by
  have h := center_statedSp_eq_bot_of_charP_two (m := n) (F := K) hn
  rwa [show Subgroup.center (StatedSp n K) =
      (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) from by
    rw [show StatedSp n K = TauCeti.GLSymplectic (Fin n) K from
      statedSp_eq_GLSymplectic (n := n) (K := K)]
    exact center_GLSymplectic_eq (n := n) (K := K)] at h

private noncomputable def k328dps2_projEquiv {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (hn : 1 ≤ n) : StatedProj (StatedSp n K) ≃* StatedSp n K :=
  (QuotientGroup.quotientMulEquivOfEq (k328dps2_scalars_bot (n := n) (K := K) hn)).trans
    (QuotientGroup.quotientBot (G := StatedSp n K))

private theorem k328dps2_comp_map {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {L K : Subgroup G} (h : CFSG.Assembly.IsComponentOf L K) :
    CFSG.Assembly.IsComponentOf (L.map f) (K.map f) :=
  ⟨Subgroup.map_mono h.1, CFSG.Assembly.IsSubnormal.map f h.2.1,
    (CFSG.Assembly.IsQuasisimple.congr (L.equivMapOfInjective f hf)).1 h.2.2⟩

private theorem k328dps2_bound_sl {f c : ℕ}
    (h : (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) = c) (hc : c < 2 ^ 24) :
    f ≤ 7 := by
  by_contra hf
  push Not at hf
  have hq : (2 : ℕ) ^ 8 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq3 : ((2 : ℕ) ^ 8) ^ 3 ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left hq 3
  have hq2 : 1 < (2 ^ f) ^ 2 := by
    have : 2 ≤ 2 ^ f := le_trans (by norm_num : (2 : ℕ) ≤ 2 ^ 8) hq
    nlinarith
  have hq3' : 1 < (2 ^ f) ^ 3 := by nlinarith
  have hpos : 0 < ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) :=
    Nat.mul_pos (by omega) (by omega)
  have hle : (2 ^ f) ^ 3 ≤ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
    simpa using Nat.mul_le_mul_left ((2 ^ f) ^ 3) (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hpos))
  rw [h] at hle
  have hc' : c < 2 ^ 24 := hc
  norm_num at hc'
  have := le_trans hq3 hle
  norm_num at this
  omega

private theorem k328dps2_bound_su {f c : ℕ}
    (h : (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) = c) (hc : c < 2 ^ 24) :
    f ≤ 7 := by
  by_contra hf
  push Not at hf
  have hq : (2 : ℕ) ^ 8 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq3 : ((2 : ℕ) ^ 8) ^ 3 ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left hq 3
  have hq2 : 1 < (2 ^ f) ^ 2 := by
    have : 2 ≤ 2 ^ f := le_trans (by norm_num : (2 : ℕ) ≤ 2 ^ 8) hq
    nlinarith
  have hq3' : 1 < (2 ^ f) ^ 3 := by nlinarith
  have hpos : 0 < ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) :=
    Nat.mul_pos (by omega) (by positivity)
  have hle : (2 ^ f) ^ 3 ≤ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
    simpa using Nat.mul_le_mul_left ((2 ^ f) ^ 3) (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hpos))
  rw [h] at hle
  have hc' : c < 2 ^ 24 := hc
  norm_num at hc'
  have := le_trans hq3 hle
  norm_num at this
  omega

private theorem k328dps2_sl3_six0480 {f : ℕ}
    (h : (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) = 60480) : f = 2 := by
  have hf := k328dps2_bound_sl h (by norm_num)
  interval_cases f <;> simp_all

private theorem k328dps2_sl3_ne_16547328 {f : ℕ}
    (h : (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) = 16547328) : False := by
  have hf := k328dps2_bound_sl h (by norm_num)
  interval_cases f <;> simp_all

private theorem k328dps2_su3_ne_60480 {f : ℕ}
    (h : (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) = 60480) : False := by
  have hf := k328dps2_bound_su h (by norm_num)
  interval_cases f <;> simp_all

private theorem k328dps2_su3_16547328 {f : ℕ}
    (h : (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) = 16547328) : f = 3 := by
  have hf := k328dps2_bound_su h (by norm_num)
  interval_cases f <;> simp_all

private theorem k328dps2_block {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ} (hn : n ≤ 3)
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {X : Subgroup (StatedSp n K)}
    (hX : CFSG.Assembly.IsComponentOf X
      ((Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap (StatedSp n K).subtype))
    (hcen : Nat.card (Subgroup.center ↥X) = 3)
    (hXcard : Nat.card X = 60480 ∨ Nat.card X = 16547328) :
    (∃ (d : ℕ) (E : Type) (_ : Field E) (_ : Fintype E) (_ : CharP E 2),
       1 ≤ d ∧ Nat.card E = Nat.card K ^ d ∧ d * 3 ≤ n ∧
       Nonempty (↥X ≃* ↥(StatedSL 3 E))) ∨
    (∃ (d : ℕ) (E : Type) (_ : Field E) (_ : Fintype E) (_ : CharP E 2),
       1 ≤ d ∧ Nat.card E = (Nat.card K ^ d) ^ 2 ∧ d * 3 ≤ n ∧
       Nonempty (↥X ≃* ↥(StatedSU 3 (Nat.card K ^ d) E))) := by
  classical
  obtain ⟨ε, hε, hJε⟩ :=
    CFSG.StandardType.ClassicalPosition.exists_isComponentOf_glBlockCentralizer_PSp
      n K {b} (by
        intro s hs s' hs'
        rw [Set.mem_singleton_iff] at hs hs'
        rw [hs, hs']) hX
  let G : Subgroup (StatedSp n K) :=
    CFSG.StandardType.ClassicalPosition.glBlockCentralizer (StatedSp n K).subtype {b} ε
  have hcompG : CFSG.Assembly.IsComponentOf X G := by
    refine ⟨hJε.1.trans (Subgroup.commutator_le_self G), ?_, hJε.2.2⟩
    have hnorm : (⁅G, G⁆.subgroupOf G).Normal := by
      have h := Subgroup.normal_subgroupOf_commutator_sup (H₁ := G) (H₂ := G)
      rwa [sup_idem] at h
    exact CFSG.Assembly.IsSubnormal.trans hJε.2.1
      (CFSG.Assembly.IsSubnormal.step (Subgroup.commutator_le_self G) hnorm
        (CFSG.Assembly.IsSubnormal.refl G))
  let Gm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.fromBlocks 0 1 (-1) 0
  have hGdet : IsUnit Gm.det := by
    have hJG : Gm = Matrix.J (Fin n) K := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [Gm, Matrix.J, Matrix.fromBlocks, Matrix.one_apply, Matrix.neg_apply,
          CharTwo.neg_eq]
    rw [hJG]
    exact Matrix.isUnit_det_J (Fin n) K
  have hGt : Matrix.transpose Gm = Gm := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Gm, Matrix.fromBlocks, Matrix.transpose_apply, Matrix.one_apply, Matrix.neg_apply,
        CharTwo.neg_eq, eq_comm]
  have hScomm : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)),
      ∀ s' ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hSU : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)),
      Matrix.transpose (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * Gm *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Gm := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa [Gm] using CFSG.Open.StatedAPI.mem_statedSp_iff.mp hb
  have hSUmap : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)),
      Matrix.transpose ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map (RingHom.id K)) * Gm *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Gm := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa [Gm, Matrix.map_id] using CFSG.Open.StatedAPI.mem_statedSp_iff.mp hb
  obtain ⟨e, he, heε, -⟩ :=
    CFSG.StandardType.ClassicalPosition.exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K)
      (fun _ => rfl) (G := Gm) hGdet (by simpa [Matrix.map_id] using hGt) hScomm hSUmap hε
  have hsub_comp : CFSG.Assembly.IsComponentOf (X.subgroupOf G) (⊤ : Subgroup ↥G) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact CFSG.Assembly.IsSubnormal.top_iff.mpr
        ((CFSG.Assembly.IsSubnormal.iff_subgroupOf hcompG.1).1 hcompG.2.1)
    · exact (CFSG.Assembly.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hcompG.1)).2
        hcompG.2.2
  have hdm_of_rank : ∀ {d m : ℕ},
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) → d * m ≤ n := by
    intro d m hrank
    have hle : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ≤ 2 * n := by
      calc Module.finrank K (LinearMap.range (Matrix.toLin' ε))
          ≤ Module.finrank K (Fin n ⊕ Fin n → K) := Submodule.finrank_le _
        _ = 2 * n := by
            rw [Module.finrank_fintype_fun_eq_card]
            simp [Fintype.card_sum, Fintype.card_fin, two_mul]
    nlinarith
  rcases CFSG.StandardType.TableC.isPrimIdemIn_cases hGdet hGt hScomm hSU hε he heε with
    heq | ⟨-, e', he', hne', hεe⟩
  · have heprim : CFSG.StandardType.ClassicalPosition.IsPrimIdemIn
        (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε := heq ▸ he
    by_cases h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε
    ·
      obtain ⟨n₁, -, ⟨iso⟩⟩ := CFSG.StandardType.ClassicalBlocks.blockGroup_iso_Sp_one b hb hodd hε h1
      exfalso
      let φ : G ≃* StatedSp n₁ K := iso
      have hsub_comp₁ : CFSG.Assembly.IsComponentOf (X.subgroupOf G) (⊤ : Subgroup ↥G) := hsub_comp
      have hC : CFSG.Assembly.IsComponentOf ((X.subgroupOf G).map φ.toMonoidHom)
          (⊤ : Subgroup (StatedSp n₁ K)) := by
        have h := k328dps2_comp_map φ.toMonoidHom φ.injective hsub_comp₁
        rwa [Subgroup.map_top_of_surjective _ φ.surjective] at h
      have hXle : Nat.card X ≤ Nat.card (StatedSp n₁ K) := by
        have h1card : Nat.card X = Nat.card ((X.subgroupOf G).map φ.toMonoidHom) := by
          rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcompG.1).toEquiv]
          exact Nat.card_congr (φ.subgroupMap (X.subgroupOf G)).toEquiv
        rw [h1card]
        exact Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_subgroup_dvd_card _)
      have hXge : 60480 ≤ Nat.card X := by rcases hXcard with h | h <;> omega
      by_cases hsmall : n₁ = 0 ∨ (n₁ = 1 ∧ Nat.card K = 2) ∨ (n₁ = 2 ∧ Nat.card K = 2)
      · have hXle' : Nat.card X ≤ Fintype.card (StatedSp n₁ K) := by
          rw [← Nat.card_eq_fintype_card]; exact hXle
        have hbound : Fintype.card (StatedSp n₁ K) ≤ 1024 := by
          have hb_le := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.card_statedSp_le (K := K) n₁
          rw [Nat.card_eq_fintype_card] at hb_le
          rcases hsmall with rfl | ⟨rfl, hK2⟩ | ⟨rfl, hK2⟩
          · norm_num at hb_le; omega
          · have hK2' : Nat.card K = 2 := hK2
            rw [hK2'] at hb_le; norm_num at hb_le; omega
          · have hK2' : Nat.card K = 2 := hK2
            rw [hK2'] at hb_le; norm_num at hb_le; omega
        omega
      · have hn₁1 : 1 ≤ n₁ := by
          rcases Nat.eq_zero_or_pos n₁ with h0 | hpos
          · exact absurd (Or.inl h0) hsmall
          · exact hpos
        have h1' : ¬ (n₁ = 1 ∧ Nat.card K = 2) := fun h => hsmall (Or.inr (Or.inl h))
        have h2' : ¬ (n₁ = 2 ∧ Nat.card K = 2) := fun h => hsmall (Or.inr (Or.inr h))
        have hqsSp : CFSG.Assembly.IsQuasisimple (StatedSp n₁ K) :=
          (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
            (CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp.isQuasisimple_statedSp_of_not_small
              hn₁1 h1' h2')
        have hqsTop : CFSG.Assembly.IsQuasisimple ↥(⊤ : Subgroup (StatedSp n₁ K)) :=
          (CFSG.Assembly.IsQuasisimple.congr Subgroup.topEquiv).2 hqsSp
        have hCtop : (X.subgroupOf G).map φ.toMonoidHom = ⊤ :=
          CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple hqsTop hC
        have hXsub_top : X.subgroupOf G = ⊤ :=
          Subgroup.map_injective (f := φ.toMonoidHom) φ.injective (by
            rw [hCtop, Subgroup.map_top_of_surjective _ φ.surjective])
        have hXtop : X = G := le_antisymm hcompG.1 (Subgroup.subgroupOf_eq_top.mp hXsub_top)
        have hcenG : Nat.card (Subgroup.center ↥G) = 1 := by
          rw [show Nat.card (Subgroup.center ↥G) =
              Nat.card (Subgroup.center ↥(StatedSp n₁ K)) from
            Nat.card_congr (Subgroup.centerCongr φ).toEquiv,
            CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := n₁) (F := K)
              hn₁1, Subgroup.card_bot]
        have hcenX : Nat.card (Subgroup.center ↥X) = 1 := by rw [hXtop]; exact hcenG
        omega
    ·
      obtain ⟨d, m, E, hEfield, hEfin, hd1, hEcard, hrank, hdeg, ⟨iso⟩⟩ :=
        CFSG.StandardType.ClassicalBlocks.blockGroup_iso_Sp_unitary b hb hodd hε heprim h1
      let : Field E := hEfield
      let : Fintype E := hEfin
      let Q : ℕ := Fintype.card K ^ d
      obtain ⟨fk, -, hKcard2⟩ := FiniteField.card K 2
      have hEchar2 : CharP E 2 := by
        refine charP_of_card_eq_prime_pow (p := 2) (f := 2 * ((fk : ℕ) * d)) ?_
        rw [hEcard, hKcard2]
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      have : CharP E 2 := hEchar2
      have hdm : d * m ≤ n := hdm_of_rank hrank
      let φ : G ≃* GUFull m Q E := iso
      have hC : CFSG.Assembly.IsComponentOf ((X.subgroupOf G).map φ.toMonoidHom)
          (⊤ : Subgroup ↥(GUFull m Q E)) := by
        have h := k328dps2_comp_map φ.toMonoidHom φ.injective hsub_comp
        rwa [Subgroup.map_top_of_surjective _ φ.surjective] at h
      have hmapGU : CFSG.Assembly.IsComponentOf
          (((X.subgroupOf G).map φ.toMonoidHom).map (GUFull m Q E).subtype) (GUFull m Q E) := by
        have h := k328dps2_comp_map (GUFull m Q E).subtype (GUFull m Q E).subtype_injective hC
        rwa [Subgroup.map_top, Subgroup.range_subtype] at h
      have hEsu : Nat.card E = Q ^ 2 := by
        rw [Nat.card_eq_fintype_card, hEcard]
      have hEq := CFSG.StandardType.eq_statedSU_of_isComponentOf_unitaryFull
        (m := m) (Q := Q) (E := E) hEsu hmapGU
      have hXiso : Nonempty (↥X ≃* ↥(StatedSU m Q E)) :=
        ⟨(Subgroup.subgroupOfEquivOfLe hcompG.1).symm.trans
          ((φ.subgroupMap (X.subgroupOf G)).trans
            ((Subgroup.equivMapOfInjective ((X.subgroupOf G).map φ.toMonoidHom)
              (GUFull m Q E).subtype (GUFull m Q E).subtype_injective).trans
              (MulEquiv.subgroupCongr hEq)))⟩
      let eX : ↥X ≃* ↥(StatedSU m Q E) := Classical.choice hXiso
      have hcenSU : Nat.card (Subgroup.center ↥(StatedSU m Q E)) = 3 := by
        rw [← hcen]
        exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).symm
      have hqsE : CFSG.Assembly.IsQuasisimple ↥(StatedSU m Q E) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
          ((CFSG.Open.IsQuasisimple.congr eX).1
            ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
              hcompG.2.2))
      have hm2 : 2 ≤ m :=
        CFSG.LieType.SemisimpleCentralizers.OrderThree.two_le_of_isQuasisimple_statedSU hqsE
      have hQpow : Q = 2 ^ ((fk : ℕ) * d) := by
        dsimp only [Q]
        rw [hKcard2, ← pow_mul]
      have hEsu2 : Nat.card E = (2 ^ ((fk : ℕ) * d)) ^ 2 := by
        rw [Nat.card_eq_fintype_card, hEcard, hKcard2]
        congr 1
        rw [← pow_mul]
      have hmne2 : m ≠ 2 := by
        intro hm
        subst hm
        rw [hQpow] at hcenSU
        have h3 : Nat.card (Subgroup.center ↥(StatedSU 2 (2 ^ ((fk : ℕ) * d)) E)) = 3 := hcenSU
        rw [CFSG.ComponentClassification.RankTwoClassical.center_statedSU_two_eq_bot
            (K := E) (f := (fk : ℕ) * d) hEsu2, Subgroup.card_bot] at h3
        omega
      have hmle : m ≤ n := by
        calc m = 1 * m := (one_mul m).symm
          _ ≤ d * m := Nat.mul_le_mul_right m hd1
          _ ≤ n := hdm
      have hm3 : m = 3 := by omega
      have hd_eq1 : d = 1 := by
        have : d * 3 ≤ n := by simpa [hm3] using hdm
        omega
      have hEcardN : Nat.card E = (Nat.card K ^ d) ^ 2 := by
        simpa only [Nat.card_eq_fintype_card] using hEcard
      refine Or.inr ⟨d, E, hEfield, hEfin, hEchar2, hd1, hEcardN, ?_, ?_⟩
      · simpa [hm3] using hdm
      · have hQnat : Q = Nat.card K ^ d := by
          dsimp only [Q]
          rw [← Nat.card_eq_fintype_card]
        exact hm3 ▸ hQnat ▸ hXiso
  ·
    obtain ⟨d, m, E, hEfield, hEfin, hd1, hEcard, hrank, hdeg, ⟨iso⟩⟩ :=
      CFSG.StandardType.ClassicalBlocks.blockGroup_iso_Sp_linear b hb hodd hε he he' hne' hεe
    let : Field E := hEfield
    let : Fintype E := hEfin
    have hdm : d * m ≤ n := hdm_of_rank hrank
    let φ : G ≃* GL (Fin m) E := iso
    have hC : CFSG.Assembly.IsComponentOf ((X.subgroupOf G).map φ.toMonoidHom)
        (⊤ : Subgroup (GL (Fin m) E)) := by
      have h := k328dps2_comp_map φ.toMonoidHom φ.injective hsub_comp
      rwa [Subgroup.map_top_of_surjective _ φ.surjective] at h
    have hEq := CFSG.StandardType.eq_statedSL_of_isComponentOf_top hC
    have hXiso : Nonempty (↥X ≃* ↥(StatedSL m E)) :=
      ⟨(Subgroup.subgroupOfEquivOfLe hcompG.1).symm.trans
        ((φ.subgroupMap (X.subgroupOf G)).trans (MulEquiv.subgroupCongr hEq))⟩
    let eX : ↥X ≃* ↥(StatedSL m E) := Classical.choice hXiso
    have hcenSL : Nat.card (Subgroup.center ↥(StatedSL m E)) = 3 := by
      rw [← hcen]
      exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).symm
    have hqsE : CFSG.Assembly.IsQuasisimple ↥(StatedSL m E) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
        ((CFSG.Open.IsQuasisimple.congr eX).1
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
            hcompG.2.2))
    have hm2 : 2 ≤ m :=
      CFSG.LieType.SemisimpleCentralizers.OrderThree.two_le_of_isQuasisimple_statedSL hqsE
    obtain ⟨fk, -, hKcard2⟩ := FiniteField.card K 2
    have hEchar2 : CharP E 2 := by
      refine charP_of_card_eq_prime_pow (p := 2) (f := (fk : ℕ) * d) ?_
      rw [hEcard, hKcard2, ← pow_mul]
    have : CharP E 2 := hEchar2
    have hmne2 : m ≠ 2 := by
      intro hm
      subst hm
      have h3 : Nat.card (Subgroup.center ↥(StatedSL 2 E)) = 3 := hcenSL
      rw [CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq 2,
          CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot, Subgroup.card_bot] at h3
      omega
    have hmle : m ≤ n := by
      calc m = 1 * m := (one_mul m).symm
        _ ≤ d * m := Nat.mul_le_mul_right m hd1
        _ ≤ n := hdm
    have hm3 : m = 3 := by omega
    have hd_eq1 : d = 1 := by
      have : d * 3 ≤ n := by simpa [hm3] using hdm
      omega
    have hEcardN : Nat.card E = Nat.card K ^ d := by
      simpa only [Nat.card_eq_fintype_card] using hEcard
    refine Or.inl ⟨d, E, hEfield, hEfin, hEchar2, hd1, hEcardN, ?_, ?_⟩
    · simpa [hm3] using hdm
    · exact hm3 ▸ hXiso

theorem k328det_famPSpTwo :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n f : ℕ, (n = 2 ∨ n = 3) →
      LieModel S .PSp n 2 f → K328DetPosIn S → LieModel S .PSp 3 2 2 ∨ LieModel S .PSp 3 2 3 := by
  intro S _ _ hSsimp n f hn hLie hPos
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨eS⟩⟩ := hLie.statedClassicalModel (by decide)
  let : Field K := hKfield
  let : Finite K := hKfin
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := k328dps2_charP hKcard
  have hnpos : 1 ≤ n := by rcases hn with h | h <;> omega
  let eProj : StatedProj (StatedSp n K) ≃* StatedSp n K := k328dps2_projEquiv hnpos
  let eAll : S ≃* StatedSp n K := eS.trans eProj
  obtain ⟨Z0, X0, hpos0, hX0ne⟩ := hPos
  have hpos : Pos (StatedSp n K) (Z0.map eAll.toMonoidHom) (X0.map eAll.toMonoidHom) :=
    pos_map eAll hpos0
  have hXne : X0.map eAll.toMonoidHom ≠ ⊤ := by
    intro h
    refine hX0ne ?_
    have h' : X0.map eAll.toMonoidHom = (⊤ : Subgroup S).map eAll.toMonoidHom := by
      rw [Subgroup.map_top_of_surjective _ eAll.surjective, h]
    exact Subgroup.map_injective (f := eAll.toMonoidHom) eAll.injective h'
  set Z : Subgroup (StatedSp n K) := Z0.map eAll.toMonoidHom
  set X : Subgroup (StatedSp n K) := X0.map eAll.toMonoidHom
  have hXcard : Nat.card X = 60480 ∨ Nat.card X = 16547328 :=
    k328det_posCard (StatedSp n K) Z X hpos
  obtain ⟨hZcard, hZX, hXC, hsub, hqs, hcen, hlie⟩ := hpos
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hborder⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZcard])
  have hb3 : orderOf (b : StatedSp n K) = 3 := by rw [Subgroup.orderOf_coe, hborder]
  have hZgen : Z = Subgroup.zpowers (b : StatedSp n K) := by
    have hle : Subgroup.zpowers (b : StatedSp n K) ≤ Z := Subgroup.zpowers_le.mpr b.2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hb3, hZcard])).symm
  let bG : GL (Fin n ⊕ Fin n) K := ((b : StatedSp n K) : GL (Fin n ⊕ Fin n) K)
  have hbG : bG ∈ StatedSp n K := (b : StatedSp n K).2
  have hbGord : orderOf bG = 3 := by
    change orderOf (((b : StatedSp n K)) : GL (Fin n ⊕ Fin n) K) = 3
    rw [Subgroup.orderOf_coe, hb3]
  have hodd : Odd (orderOf bG) := by rw [hbGord]; decide
  have hcent_eq : (Subgroup.centralizer ({bG} : Set (GL (Fin n ⊕ Fin n) K))).comap
      (StatedSp n K).subtype = Subgroup.centralizer (Z : Set (StatedSp n K)) := by
    rw [hZgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff]
    constructor
    · rintro h y rfl
      exact Subtype.ext (by
        change (((b : StatedSp n K)) : GL (Fin n ⊕ Fin n) K) * ((x : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
          ((x : StatedSp n K) : GL (Fin n ⊕ Fin n) K) * (((b : StatedSp n K)) : GL (Fin n ⊕ Fin n) K)
        exact h bG rfl)
    · rintro h y rfl
      exact congrArg Subtype.val (h (b : StatedSp n K) rfl)
  have hcomp : CFSG.Assembly.IsComponentOf X
      ((Subgroup.centralizer ({bG} : Set (GL (Fin n ⊕ Fin n) K))).comap
        (StatedSp n K).subtype) := by
    rw [hcent_eq]
    refine (CFSG.Assembly.isComponentOf_iff_open).mpr ⟨hXC, ?_, ?_⟩
    · exact (CFSG.Open.IsSubnormal.iff_subgroupOf hXC).mpr hsub
    · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥X).mpr hqs
  have hnle : n ≤ 3 := by rcases hn with h | h <;> omega
  rcases k328dps2_block hnle bG hbG hodd hcomp hcen hXcard with
    ⟨d, E, hEfield, hEfin, hEchar, hd1, hEcard, hdb, ⟨eX⟩⟩ |
    ⟨d, E, hEfield, hEfin, hEchar, hd1, hEcard, hdb, ⟨eX⟩⟩
  · let : Field E := hEfield
    let : Fintype E := hEfin
    let : CharP E 2 := hEchar
    have hn3 : n = 3 := by omega
    subst hn3
    have hd_eq1 : d = 1 := by omega
    have eX3 : ↥X ≃* ↥(StatedSL 3 E) := eX
    have hXsl : Nat.card (StatedSL 3 E) = 60480 ∨ Nat.card (StatedSL 3 E) = 16547328 := by
      rw [← Nat.card_congr eX3.toEquiv]; exact hXcard
    have hE2f : Nat.card E = 2 ^ f := by rw [hEcard, hd_eq1, pow_one, hKcard]
    have hcardSL : Nat.card (StatedSL 3 E) =
        (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
      rw [CFSG.Open.StatedAPI.card_statedSL_three, hE2f]
    have hf2 : f = 2 := by
      rcases hXsl with h | h
      · exact k328dps2_sl3_six0480 (by rwa [hcardSL] at h)
      · exact (k328dps2_sl3_ne_16547328 (by rwa [hcardSL] at h)).elim
    refine Or.inl ?_
    have hK4 : Nat.card K = 2 ^ 2 := by rw [hKcard, hf2]
    have hmodel : StatedClassicalModel (StatedSp 3 K) .PSp 3 2 2 :=
      ⟨⟨Nat.prime_two, by norm_num, by norm_num, by norm_num⟩, K, hKfield, hKfin, hK4,
        ⟨eProj.symm⟩⟩
    exact LieModel.of_mulEquiv eAll.symm (Or.inl ⟨by decide, hmodel⟩)
  · let : Field E := hEfield
    let : Fintype E := hEfin
    let : CharP E 2 := hEchar
    have hn3 : n = 3 := by omega
    subst hn3
    have hd_eq1 : d = 1 := by omega
    subst hd_eq1
    have eX3 : ↥X ≃* ↥(StatedSU 3 (Nat.card K) E) := by
      rw [← pow_one (Nat.card K)]
      exact eX
    have hXsu : Nat.card (StatedSU 3 (Nat.card K) E) = 60480 ∨
        Nat.card (StatedSU 3 (Nat.card K) E) = 16547328 := by
      rw [← Nat.card_congr eX3.toEquiv]; exact hXcard
    have hEcard' : Nat.card E = (Nat.card K) ^ 2 := by rw [hEcard, pow_one]
    have hcardSU : Nat.card (StatedSU 3 (Nat.card K) E) =
        (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.card_statedSU_three_of' (K := E)
        (q := Nat.card K) hEcard', hKcard]
      ring
    have hf3 : f = 3 := by
      rcases hXsu with h | h
      · exact (k328dps2_su3_ne_60480 (by rwa [hcardSU] at h)).elim
      · exact k328dps2_su3_16547328 (by rwa [hcardSU] at h)
    refine Or.inr ?_
    have hK8 : Nat.card K = 2 ^ 3 := by rw [hKcard, hf3]
    have hmodel : StatedClassicalModel (StatedSp 3 K) .PSp 3 2 3 :=
      ⟨⟨Nat.prime_two, by norm_num, by norm_num, by norm_num⟩, K, hKfield, hKfin, hK8,
        ⟨eProj.symm⟩⟩
    exact LieModel.of_mulEquiv eAll.symm (Or.inl ⟨by decide, hmodel⟩)

open CFSG.Open (StatedOmega StatedQuadMinus)

private lemma k328dom2_omegaPolarGram_isometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) {b : GL ι K} (hb : b ∈ StatedOmega ⇑Φ) :
    Matrix.transpose ((b : Matrix ι ι K).map (RingHom.id K)) *
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) * (b : Matrix ι ι K) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
  have hg : ∀ v : ι → K, Φ (Matrix.mulVec (b : Matrix ι ι K) v) = Φ v :=
    fun v => CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega
      (f := ⇑Φ) hb v
  have h := CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.gram_invariant (Q := Φ) hg
  simpa [Matrix.map_id,
    CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.polarGram_eq_toMatrix₂'] using h

private theorem k328dom2_bound_six {f c : ℕ}
    (h : (2 ^ f) ^ 6 ≤ c) (hc : c < 2 ^ 24) : f ≤ 3 := by
  by_contra hf
  push Not at hf
  have h4 : (2 : ℕ) ^ 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h24 : ((2 : ℕ) ^ 4) ^ 6 ≤ (2 ^ f) ^ 6 := Nat.pow_le_pow_left h4 6
  have h24' : (2 : ℕ) ^ 24 ≤ c := by
    calc (2 : ℕ) ^ 24 = ((2 : ℕ) ^ 4) ^ 6 := by norm_num
      _ ≤ (2 ^ f) ^ 6 := h24
      _ ≤ c := h
  omega

private theorem k328dom2_sl4_ne {f : ℕ} (hf : 1 ≤ f) :
    (2 ^ f) ^ 6 * (((2 ^ f) ^ 2 - 1) * (((2 ^ f) ^ 3 - 1) * ((2 ^ f) ^ 4 - 1))) ≠ 60480 ∧
    (2 ^ f) ^ 6 * (((2 ^ f) ^ 2 - 1) * (((2 ^ f) ^ 3 - 1) * ((2 ^ f) ^ 4 - 1))) ≠ 16547328 := by
  have hq2 : 2 ≤ (2 : ℕ) ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2 : 0 < (2 ^ f) ^ 2 - 1 := by
    have := Nat.pow_le_pow_left hq2 2
    norm_num at this
    omega
  have h3 : 0 < (2 ^ f) ^ 3 - 1 := by
    have := Nat.pow_le_pow_left hq2 3
    norm_num at this
    omega
  have h4 : 0 < (2 ^ f) ^ 4 - 1 := by
    have := Nat.pow_le_pow_left hq2 4
    norm_num at this
    omega
  have hpos : 0 < ((2 ^ f) ^ 2 - 1) * (((2 ^ f) ^ 3 - 1) * ((2 ^ f) ^ 4 - 1)) :=
    Nat.mul_pos h2 (Nat.mul_pos h3 h4)
  have hle : (2 ^ f) ^ 6 ≤
      (2 ^ f) ^ 6 * (((2 ^ f) ^ 2 - 1) * (((2 ^ f) ^ 3 - 1) * ((2 ^ f) ^ 4 - 1))) := by
    simpa using Nat.mul_le_mul_left ((2 ^ f) ^ 6)
      (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hpos))
  constructor
  · intro heq
    have hf3 : f ≤ 3 := k328dom2_bound_six hle (by rw [heq]; norm_num)
    interval_cases f <;> norm_num at heq
  · intro heq
    have hf3 : f ≤ 3 := k328dom2_bound_six hle (by rw [heq]; norm_num)
    interval_cases f <;> norm_num at heq

private theorem k328dom2_su4_ne {f : ℕ} (hf : 1 ≤ f) :
    (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1) ≠ 60480 ∧
    (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1) ≠ 16547328 := by
  have hq2 : 2 ≤ (2 : ℕ) ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2 : 1 ≤ (2 ^ f) ^ 2 - 1 := by
    have := Nat.pow_le_pow_left hq2 2
    norm_num at this
    omega
  have h3 : 1 ≤ (2 ^ f) ^ 3 + 1 := by omega
  have h4 : 1 ≤ (2 ^ f) ^ 4 - 1 := by
    have := Nat.pow_le_pow_left hq2 4
    norm_num at this
    omega
  have hstep : (2 ^ f) ^ 6 ≤ (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) := by
    simpa using Nat.mul_le_mul_left ((2 ^ f) ^ 6) h2
  have hstep2 : (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) ≤
      (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) := by
    simpa using Nat.mul_le_mul_left ((2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1)) h3
  have hle : (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) ≤
      (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1) := by
    simpa using Nat.mul_le_mul_left
      ((2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) h4
  have hge : (2 ^ f) ^ 6 ≤
      (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1) :=
    hstep.trans (hstep2.trans hle)
  constructor
  · intro heq
    have hf3 : f ≤ 3 := k328dom2_bound_six hge (by rw [heq]; norm_num)
    interval_cases f <;> norm_num at heq
  · intro heq
    have hf3 : f ≤ 3 := k328dom2_bound_six hge (by rw [heq]; norm_num)
    interval_cases f <;> norm_num at heq

private theorem k328dom2_block {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K]
    [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : Fintype.card ι = 8) (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hb3 : orderOf b = 3)
    {X : Subgroup (StatedOmega ⇑Φ)}
    (hX : CFSG.Assembly.IsComponentOf X
      ((Subgroup.centralizer ({b} : Set (GL ι K))).comap (StatedOmega ⇑Φ).subtype))
    (hbX : (⟨b, hb⟩ : StatedOmega ⇑Φ) ∈ X)
    (hcen : Nat.card (Subgroup.center ↥X) = 3)
    (hXcard : Nat.card X = 60480 ∨ Nat.card X = 16547328) :
    (∃ (E : Type) (_ : Field E) (_ : Fintype E) (_ : CharP E 2),
       Nat.card E = Nat.card K ∧ Nonempty (↥X ≃* ↥(StatedSL 3 E))) ∨
    (∃ (E : Type) (_ : Field E) (_ : Fintype E) (_ : CharP E 2),
       Nat.card E = Nat.card K ^ 2 ∧ Nonempty (↥X ≃* ↥(StatedSU 3 (Nat.card K) E))) := by
  classical
  have hodd : Odd (orderOf b) := by rw [hb3]; decide
  obtain ⟨P, hP, -, -, hc, hsup, -⟩ :=
    CFSG.StandardType.ClassicalBlocks.centralizer_block_decomp_Omega Φ hΦ (by omega) b hb hodd
  rw [← hsup] at hX
  obtain ⟨ε, hεP, hcompG⟩ :=
    CFSG.StandardType.exists_isComponentOf_block P
      (fun ε => glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) hc hX
  have hε := hP ε hεP
  let G : Subgroup (StatedOmega ⇑Φ) := glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε
  have hsub_comp : CFSG.Assembly.IsComponentOf (X.subgroupOf G) (⊤ : Subgroup ↥G) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact CFSG.Assembly.IsSubnormal.top_iff.mpr
        ((CFSG.Assembly.IsSubnormal.iff_subgroupOf hcompG.1).1 hcompG.2.1)
    · exact (CFSG.Assembly.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hcompG.1)).2
        hcompG.2.2
  have hdm_of_rank : ∀ {d m : ℕ},
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) → d * m ≤ 4 := by
    intro d m hrank
    have hle : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ≤ Fintype.card ι := by
      calc Module.finrank K (LinearMap.range (Matrix.toLin' ε))
          ≤ Module.finrank K (ι → K) := Submodule.finrank_le _
        _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
    rw [h8] at hle
    nlinarith
  let Gm : Matrix ι ι K := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
  have hG : IsUnit Gm.det := CFSG.StandardType.TableC.polarGram_isUnit_det Φ hΦ
  have hGt : Matrix.transpose Gm = Gm := CFSG.StandardType.TableC.polarGram_transpose Φ
  have hS : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hSU : ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose (s : Matrix ι ι K) * Gm * (s : Matrix ι ι K) = Gm := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa [Gm, Matrix.map_id] using k328dom2_omegaPolarGram_isometry Φ hb
  have hSUmap : ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose ((s : Matrix ι ι K).map (RingHom.id K)) * Gm *
        (s : Matrix ι ι K) = Gm := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa [Gm] using k328dom2_omegaPolarGram_isometry Φ hb
  obtain ⟨e, he, heε, -⟩ :=
    CFSG.StandardType.ClassicalPosition.exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K)
      (fun _ => rfl) (G := Gm) hG (by simpa [Matrix.map_id] using hGt) hS hSUmap hε
  rcases CFSG.StandardType.TableC.isPrimIdemIn_cases hG hGt hS hSU hε he heε with
    heq | ⟨-, e', he', hne', hεe⟩
  · have heprim : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε :=
      heq ▸ he
    by_cases h1 : (b : Matrix ι ι K) * ε = ε
    · exfalso
      have hbG : (b : GL ι K) ∈
          (Subgroup.centralizer ({b} : Set (GL ι K)) ⊓ glFixing (1 - ε)) := by
        have h := hcompG.1 hbX
        rw [glBlockCentralizer, Subgroup.mem_comap] at h
        simpa using h
      have hfix : (b : Matrix ι ι K) * (1 - ε) = 1 - ε := by
        have := (Subgroup.mem_inf.mp hbG).2
        simpa [glFixing] using this
      have hb1 : b = 1 := by
        apply Units.ext
        calc (b : Matrix ι ι K) = (b : Matrix ι ι K) * 1 := (mul_one _).symm
          _ = (b : Matrix ι ι K) * (ε + (1 - ε)) := by rw [add_sub_cancel]
          _ = (b : Matrix ι ι K) * ε + (b : Matrix ι ι K) * (1 - ε) := by rw [mul_add]
          _ = ε + (1 - ε) := by rw [h1, hfix]
          _ = 1 := by rw [add_sub_cancel]
      have : orderOf b = 1 := by rw [hb1, orderOf_one]
      omega
    · obtain ⟨d, m, E, hEfield, hEfin, hd1, hEcard, hrank, hdeg, ⟨iso⟩⟩ :=
        CFSG.StandardType.ClassicalBlocks.blockGroup_iso_Omega_unitary Φ hΦ (by omega) b hb hodd
          hε heprim h1
      let : Field E := hEfield
      let : Fintype E := hEfin
      let Q : ℕ := Fintype.card K ^ d
      obtain ⟨fk, -, hKcard2⟩ := FiniteField.card K 2
      have hEchar2 : CharP E 2 := by
        refine charP_of_card_eq_prime_pow (p := 2) (f := 2 * ((fk : ℕ) * d)) ?_
        rw [hEcard, hKcard2]
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      have : CharP E 2 := hEchar2
      have hdm : d * m ≤ 4 := hdm_of_rank hrank
      let φ : G ≃* GUFull m Q E := iso
      have hC : CFSG.Assembly.IsComponentOf ((X.subgroupOf G).map φ.toMonoidHom)
          (⊤ : Subgroup ↥(GUFull m Q E)) := by
        have h := k328dps2_comp_map φ.toMonoidHom φ.injective hsub_comp
        rwa [Subgroup.map_top_of_surjective _ φ.surjective] at h
      have hmapGU : CFSG.Assembly.IsComponentOf
          (((X.subgroupOf G).map φ.toMonoidHom).map (GUFull m Q E).subtype) (GUFull m Q E) := by
        have h := k328dps2_comp_map (GUFull m Q E).subtype (GUFull m Q E).subtype_injective hC
        rwa [Subgroup.map_top, Subgroup.range_subtype] at h
      have hEsu : Nat.card E = Q ^ 2 := by
        rw [Nat.card_eq_fintype_card, hEcard]
      have hEq := CFSG.StandardType.eq_statedSU_of_isComponentOf_unitaryFull
        (m := m) (Q := Q) (E := E) hEsu hmapGU
      have hXiso : Nonempty (↥X ≃* ↥(StatedSU m Q E)) :=
        ⟨(Subgroup.subgroupOfEquivOfLe hcompG.1).symm.trans
          ((φ.subgroupMap (X.subgroupOf G)).trans
            ((Subgroup.equivMapOfInjective ((X.subgroupOf G).map φ.toMonoidHom)
              (GUFull m Q E).subtype (GUFull m Q E).subtype_injective).trans
              (MulEquiv.subgroupCongr hEq)))⟩
      let eX : ↥X ≃* ↥(StatedSU m Q E) := Classical.choice hXiso
      have hcenSU : Nat.card (Subgroup.center ↥(StatedSU m Q E)) = 3 := by
        rw [← hcen]
        exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).symm
      have hqsE : CFSG.Assembly.IsQuasisimple ↥(StatedSU m Q E) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
          ((CFSG.Open.IsQuasisimple.congr eX).1
            ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
              hcompG.2.2))
      have hm2 : 2 ≤ m :=
        CFSG.LieType.SemisimpleCentralizers.OrderThree.two_le_of_isQuasisimple_statedSU hqsE
      have hQpow : Q = 2 ^ ((fk : ℕ) * d) := by
        dsimp only [Q]
        rw [hKcard2, ← pow_mul]
      have hEsu2 : Nat.card E = (2 ^ ((fk : ℕ) * d)) ^ 2 := by
        rw [Nat.card_eq_fintype_card, hEcard, hKcard2]
        congr 1
        rw [← pow_mul]
      have hmne2 : m ≠ 2 := by
        intro hm
        subst hm
        rw [hQpow] at hcenSU
        have h3 : Nat.card (Subgroup.center ↥(StatedSU 2 (2 ^ ((fk : ℕ) * d)) E)) = 3 := hcenSU
        rw [CFSG.ComponentClassification.RankTwoClassical.center_statedSU_two_eq_bot
            (K := E) (f := (fk : ℕ) * d) hEsu2, Subgroup.card_bot] at h3
        omega
      have hmle : m ≤ 4 := by
        calc m = 1 * m := (one_mul m).symm
          _ ≤ d * m := Nat.mul_le_mul_right m hd1
          _ ≤ 4 := hdm
      rcases (show m = 3 ∨ m = 4 by omega) with hm3 | hm4
      · have hd_eq1 : d = 1 := by
          have : d * 3 ≤ 4 := by simpa [hm3] using hdm
          omega
        have hEcardN : Nat.card E = (Nat.card K ^ d) ^ 2 := by
          simpa only [Nat.card_eq_fintype_card] using hEcard
        have hQnat : Q = Nat.card K := by
          dsimp only [Q]
          rw [← Nat.card_eq_fintype_card, hd_eq1, pow_one]
        refine Or.inr ⟨E, hEfield, hEfin, hEchar2, ?_, ?_⟩
        · rw [hEcardN, hd_eq1, pow_one]
        · exact hm3 ▸ hQnat ▸ hXiso
      · exfalso
        have hd_eq1 : d = 1 := by
          have : d * 4 ≤ 4 := by simpa [hm4] using hdm
          omega
        have hEcard4 : Nat.card E = (2 ^ (fk : ℕ)) ^ 2 := by
          rw [hEsu2, hd_eq1, mul_one]
        have hdat : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2
            (fk : ℕ) E :=
          CFSG.ComponentClassification.RankTwoClassical.unitaryFieldData_of_card hEcard4
            (Nat.one_le_iff_ne_zero.mpr (ne_of_gt fk.pos))
        have hQ4 : Q = 2 ^ (fk : ℕ) := by rw [hQpow, hd_eq1, mul_one]
        have hX4 : ↥X ≃* ↥(StatedSU 4 (2 ^ (fk : ℕ)) E) := hm4 ▸ (hQ4 ▸ eX)
        have hXsu4 : Nat.card (StatedSU 4 (2 ^ (fk : ℕ)) E) = 60480 ∨
            Nat.card (StatedSU 4 (2 ^ (fk : ℕ)) E) = 16547328 := by
          rw [← Nat.card_congr hX4.toEquiv]
          exact hXcard
        have hform : Nat.card (StatedSU 4 (2 ^ (fk : ℕ)) E) =
            (2 ^ (fk : ℕ)) ^ 6 * ((2 ^ (fk : ℕ)) ^ 2 - 1) * ((2 ^ (fk : ℕ)) ^ 3 + 1) *
              ((2 ^ (fk : ℕ)) ^ 4 - 1) :=
          CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four hdat
        rcases hXsu4 with h | h
        · exact (k328dom2_su4_ne (f := (fk : ℕ))
            (Nat.one_le_iff_ne_zero.mpr (ne_of_gt fk.pos))).1 (hform ▸ h)
        · exact (k328dom2_su4_ne (f := (fk : ℕ))
            (Nat.one_le_iff_ne_zero.mpr (ne_of_gt fk.pos))).2 (hform ▸ h)
  · obtain ⟨d, m, E, hEfield, hEfin, hd1, hEcard, hrank, hdeg, ⟨iso⟩⟩ :=
      CFSG.StandardType.ClassicalBlocks.blockGroup_iso_Omega_linear Φ hΦ (by omega) b hb hodd
        hε he he' hne' hεe
    let : Field E := hEfield
    let : Fintype E := hEfin
    have hdm : d * m ≤ 4 := hdm_of_rank hrank
    let φ : G ≃* GL (Fin m) E := iso
    have hC : CFSG.Assembly.IsComponentOf ((X.subgroupOf G).map φ.toMonoidHom)
        (⊤ : Subgroup (GL (Fin m) E)) := by
      have h := k328dps2_comp_map φ.toMonoidHom φ.injective hsub_comp
      rwa [Subgroup.map_top_of_surjective _ φ.surjective] at h
    have hEq := CFSG.StandardType.eq_statedSL_of_isComponentOf_top hC
    have hXiso : Nonempty (↥X ≃* ↥(StatedSL m E)) :=
      ⟨(Subgroup.subgroupOfEquivOfLe hcompG.1).symm.trans
        ((φ.subgroupMap (X.subgroupOf G)).trans (MulEquiv.subgroupCongr hEq))⟩
    let eX : ↥X ≃* ↥(StatedSL m E) := Classical.choice hXiso
    have hcenSL : Nat.card (Subgroup.center ↥(StatedSL m E)) = 3 := by
      rw [← hcen]
      exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).symm
    have hqsE : CFSG.Assembly.IsQuasisimple ↥(StatedSL m E) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
        ((CFSG.Open.IsQuasisimple.congr eX).1
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
            hcompG.2.2))
    have hm2 : 2 ≤ m :=
      CFSG.LieType.SemisimpleCentralizers.OrderThree.two_le_of_isQuasisimple_statedSL hqsE
    obtain ⟨fk, -, hKcard2⟩ := FiniteField.card K 2
    have hEchar2 : CharP E 2 := by
      refine charP_of_card_eq_prime_pow (p := 2) (f := (fk : ℕ) * d) ?_
      rw [hEcard, hKcard2, ← pow_mul]
    have : CharP E 2 := hEchar2
    have hmne2 : m ≠ 2 := by
      intro hm
      subst hm
      have h3 : Nat.card (Subgroup.center ↥(StatedSL 2 E)) = 3 := hcenSL
      rw [CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq 2,
          CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot, Subgroup.card_bot] at h3
      omega
    have hmle : m ≤ 4 := by
      calc m = 1 * m := (one_mul m).symm
        _ ≤ d * m := Nat.mul_le_mul_right m hd1
        _ ≤ 4 := hdm
    rcases (show m = 3 ∨ m = 4 by omega) with hm3 | hm4
    · have hd_eq1 : d = 1 := by
        have : d * 3 ≤ 4 := by simpa [hm3] using hdm
        omega
      have hEcardN : Nat.card E = Nat.card K ^ d := by
        simpa only [Nat.card_eq_fintype_card] using hEcard
      refine Or.inl ⟨E, hEfield, hEfin, hEchar2, ?_, ?_⟩
      · rw [hEcardN, hd_eq1, pow_one]
      · exact ⟨hm3 ▸ eX⟩
    · exfalso
      have hd_eq1 : d = 1 := by
        have : d * 4 ≤ 4 := by simpa [hm4] using hdm
        omega
      have hEK : Nat.card E = 2 ^ (fk : ℕ) := by
        have hEN : Nat.card E = Nat.card K ^ d := by
          simpa only [Nat.card_eq_fintype_card] using hEcard
        rw [hEN, Nat.card_eq_fintype_card, hKcard2, hd_eq1, pow_one]
      have hXsl4 : Nat.card (StatedSL 4 E) = 60480 ∨
          Nat.card (StatedSL 4 E) = 16547328 := by
        rw [← Nat.card_congr (hm4 ▸ eX).toEquiv]
        exact hXcard
      have hform : Nat.card (StatedSL 4 E) =
          (2 ^ (fk : ℕ)) ^ 6 *
            (((2 ^ (fk : ℕ)) ^ 2 - 1) * (((2 ^ (fk : ℕ)) ^ 3 - 1) * ((2 ^ (fk : ℕ)) ^ 4 - 1))) := by
        rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSL_four, hEK]
      rcases hXsl4 with h | h
      · exact (k328dom2_sl4_ne (f := (fk : ℕ))
          (Nat.one_le_iff_ne_zero.mpr (ne_of_gt fk.pos))).1 (hform ▸ h)
      · exact (k328dom2_sl4_ne (f := (fk : ℕ))
          (Nat.one_le_iff_ne_zero.mpr (ne_of_gt fk.pos))).2 (hform ▸ h)

theorem k328det_famPOmegaMinusTwo :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ f : ℕ,
      LieModel S .POmegaMinus 4 2 f → K328DetPosIn S →
        LieModel S .POmegaMinus 4 2 2 ∨ LieModel S .POmegaMinus 4 2 3 := by
  intro S _ _ hSsimp f hLie hPos
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, b₀, c₀, hirr, ⟨eS⟩⟩ :=
    hLie.statedClassicalModel (by decide)
  let : Field K := hKfield
  let : Finite K := hKfin
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := k328dps2_charP hKcard
  let Φ : QuadraticForm K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus 4 K b₀ c₀
  have hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (n := 4) (K := K) hirr
  have hΩ : StatedOmega ⇑Φ = StatedOmega (StatedQuadMinus 4 K b₀ c₀) := by
    dsimp only [Φ]
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
  let eProj : StatedProj (StatedOmega (StatedQuadMinus 4 K b₀ c₀)) ≃*
      StatedOmega (StatedQuadMinus 4 K b₀ c₀) :=
    CFSG.AGLEmbedding.LeviBlock.orthMinusStatedProjEquiv (K := K) (b := b₀) (c := c₀) (n := 4)
      (by norm_num)
  let eAll : S ≃* StatedOmega ⇑Φ := (eS.trans eProj).trans (MulEquiv.subgroupCongr hΩ.symm)
  obtain ⟨Z0, X0, hpos0, hX0ne⟩ := hPos
  have hpos : Pos (StatedOmega ⇑Φ) (Z0.map eAll.toMonoidHom) (X0.map eAll.toMonoidHom) :=
    pos_map eAll hpos0
  have hXne : X0.map eAll.toMonoidHom ≠ ⊤ := by
    intro h
    refine hX0ne ?_
    have h' : X0.map eAll.toMonoidHom = (⊤ : Subgroup S).map eAll.toMonoidHom := by
      rw [Subgroup.map_top_of_surjective _ eAll.surjective, h]
    exact Subgroup.map_injective (f := eAll.toMonoidHom) eAll.injective h'
  set Z : Subgroup (StatedOmega ⇑Φ) := Z0.map eAll.toMonoidHom
  set X : Subgroup (StatedOmega ⇑Φ) := X0.map eAll.toMonoidHom
  have hXcard : Nat.card X = 60480 ∨ Nat.card X = 16547328 :=
    k328det_posCard (StatedOmega ⇑Φ) Z X hpos
  obtain ⟨hZcard, hZX, hXC, hsub, hqs, hcen, hlie⟩ := hpos
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hborder⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZcard])
  have hb3 : orderOf (b : StatedOmega ⇑Φ) = 3 := by rw [Subgroup.orderOf_coe, hborder]
  have hZgen : Z = Subgroup.zpowers (b : StatedOmega ⇑Φ) := by
    have hle : Subgroup.zpowers (b : StatedOmega ⇑Φ) ≤ Z := Subgroup.zpowers_le.mpr b.2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hb3, hZcard])).symm
  let bG : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K :=
    ((b : StatedOmega ⇑Φ) : GL _ K)
  have hbG : bG ∈ StatedOmega ⇑Φ := (b : StatedOmega ⇑Φ).2
  have hbGord : orderOf bG = 3 := by
    rw [show bG = ((b : StatedOmega ⇑Φ) : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K) from rfl,
      Subgroup.orderOf_coe, hb3]
  have hodd : Odd (orderOf bG) := by rw [hbGord]; decide
  have hcent_eq : (Subgroup.centralizer ({bG} : Set (GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K))).comap
      (StatedOmega ⇑Φ).subtype = Subgroup.centralizer (Z : Set (StatedOmega ⇑Φ)) := by
    rw [hZgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  have hcomp : CFSG.Assembly.IsComponentOf X
      ((Subgroup.centralizer ({bG} : Set (GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K))).comap
        (StatedOmega ⇑Φ).subtype) := by
    rw [hcent_eq]
    refine (CFSG.Assembly.isComponentOf_iff_open).mpr ⟨hXC, ?_, ?_⟩
    · exact (CFSG.Open.IsSubnormal.iff_subgroupOf hXC).mpr hsub
    · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥X).mpr hqs
  have hbX : (b : StatedOmega ⇑Φ) ∈ X := hZX b.2
  have h8 : Fintype.card (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) = 8 := by simp
  rcases k328dom2_block Φ hΦ h8 bG hbG hbGord hcomp (by simpa using hbX) hcen hXcard with
    ⟨E, hEfield, hEfin, hEchar, hEcard, ⟨eX⟩⟩ |
    ⟨E, hEfield, hEfin, hEchar, hEcard, ⟨eX⟩⟩
  · let : Field E := hEfield
    let : Fintype E := hEfin
    let : CharP E 2 := hEchar
    have hd_eq1 : Nat.card E = Nat.card K := hEcard
    have eX3 : ↥X ≃* ↥(StatedSL 3 E) := eX
    have hXsl : Nat.card (StatedSL 3 E) = 60480 ∨ Nat.card (StatedSL 3 E) = 16547328 := by
      rw [← Nat.card_congr eX3.toEquiv]
      exact hXcard
    have hE2f : Nat.card E = 2 ^ f := by rw [hd_eq1, hKcard]
    have hcardSL : Nat.card (StatedSL 3 E) =
        (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
      rw [CFSG.Open.StatedAPI.card_statedSL_three, hE2f]
    have hf2 : f = 2 := by
      rcases hXsl with h | h
      · exact k328dps2_sl3_six0480 (by rwa [hcardSL] at h)
      · exact (k328dps2_sl3_ne_16547328 (by rwa [hcardSL] at h)).elim
    refine Or.inl ?_
    have hK4 : Nat.card K = 2 ^ 2 := by rw [hKcard, hf2]
    have hmodel : StatedClassicalModel (StatedOmega (StatedQuadMinus 4 K b₀ c₀))
        .POmegaMinus 4 2 2 :=
      ⟨⟨Nat.prime_two, by norm_num, by norm_num⟩, K, hKfield, hKfin, hK4, b₀, c₀, hirr,
        ⟨eProj.symm⟩⟩
    exact LieModel.of_mulEquiv (eS.trans eProj).symm (Or.inl ⟨by decide, hmodel⟩)
  · let : Field E := hEfield
    let : Fintype E := hEfin
    let : CharP E 2 := hEchar
    have hEcard' : Nat.card E = (Nat.card K) ^ 2 := hEcard
    have eX3 : ↥X ≃* ↥(StatedSU 3 (Nat.card K) E) := eX
    have hXsu : Nat.card (StatedSU 3 (Nat.card K) E) = 60480 ∨
        Nat.card (StatedSU 3 (Nat.card K) E) = 16547328 := by
      rw [← Nat.card_congr eX3.toEquiv]
      exact hXcard
    have hcardSU : Nat.card (StatedSU 3 (Nat.card K) E) =
        (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.card_statedSU_three_of'
        (K := E) (q := Nat.card K) hEcard', hKcard]
      ring
    have hf3 : f = 3 := by
      rcases hXsu with h | h
      · exact (k328dps2_su3_ne_60480 (by rwa [hcardSU] at h)).elim
      · exact k328dps2_su3_16547328 (by rwa [hcardSU] at h)
    refine Or.inr ?_
    have hK8 : Nat.card K = 2 ^ 3 := by rw [hKcard, hf3]
    have hmodel : StatedClassicalModel (StatedOmega (StatedQuadMinus 4 K b₀ c₀))
        .POmegaMinus 4 2 3 :=
      ⟨⟨Nat.prime_two, by norm_num, by norm_num⟩, K, hKfield, hKfin, hK8, b₀, c₀, hirr,
        ⟨eProj.symm⟩⟩
    exact LieModel.of_mulEquiv (eS.trans eProj).symm (Or.inl ⟨by decide, hmodel⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
