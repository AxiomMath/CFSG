module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
import CFSG.GH74.Generic.S1.SymBlocksUniCore
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.Certificates.CosetTableShort
import CFSG.Fischer.Uniq.CompTau
import CFSG.GH74.Generic.Front.Final
import CFSG.GH74.Generic.FrontEnd
import CFSG.GH74.Generic.S1.Defs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
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
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.QuasithinUnique.Setting
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Bridge.TableSurj
import CFSG.Sporadic.HN.LevelChainSpec
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.McL
import CFSG.Sporadic.Presentation.Common
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyChain11
import Certificates.Certificate3085Base
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.GH74.Generic.S1.SymBlocksUni
open scoped commutatorElement

private def k328r6s_iota : Fin 3 → Fin 4 := fun i => ⟨i.val, by omega⟩

private theorem k328r6s_iota_injective : Function.Injective k328r6s_iota := by
  intro a b h
  apply Fin.ext
  have hthis := congrArg Fin.val h
  simpa [k328r6s_iota] using hthis

private theorem k328r6s_charP {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 64) : CharP F 2 :=
  CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2) (n := 6) (by norm_num)
    (by rw [Nat.card_eq_fintype_card, hF]; norm_num)

private theorem k328r6s_omega_ne_one {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  intro h
  have hchar : CharP F 2 := k328r6s_charP hF
  have h3 : (3 : F) = 0 := by
    have h31 : (3 : F) = 1 + 1 + 1 := by norm_num
    rw [h31]
    simpa [h] using hω
  have h3ne : (3 : F) ≠ 0 := by
    intro h30
    have h2dvd3 : 2 ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp h30
    norm_num at h2dvd3
  exact h3ne h3

private def k328r6s_C (F : Type) [Field F] (z₀ : GL (Fin 4) F) : Subgroup (GL (Fin 4) F) :=
  StatedSU 4 8 F ⊓ Subgroup.centralizer {z₀}

private def k328r6s_Y (F : Type) [Field F] : Subgroup (GL (Fin 4) F) :=
  (StatedSU 3 8 F).map (blkGL (F := F) (ι := k328r6s_iota) k328r6s_iota_injective)

private theorem k328r6s_comm_of_mem_C {F : Type} [Field F] (z₀ : GL (Fin 4) F)
    {x : GL (Fin 4) F} (hxC : x ∈ k328r6s_C F z₀) : x * z₀ = z₀ * x :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxC).2 z₀ (Set.mem_singleton z₀)).symm

private theorem k328r6s_entry_3 {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (g : GL (Fin 4) F) (hg : g * z₀ = z₀ * g) (i : Fin 4) (hi : i.val < 3) :
    (g : Matrix (Fin 4) (Fin 4) F) i 3 = 0 := by
  have hω1 : ω ≠ 1 := k328r6s_omega_ne_one hF ω hω
  have hmul : (g : Matrix (Fin 4) (Fin 4) F) * (z₀ : Matrix (Fin 4) (Fin 4) F) =
      (z₀ : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) :=
    congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) hg
  have h := congrFun (congrFun hmul i) 3
  rw [hz, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h1 : (![ω, ω, ω, 1] : Fin 4 → F) 3 = 1 := by simp
  have h2 : (![ω, ω, ω, 1] : Fin 4 → F) i = ω := by
    fin_cases i <;> simp_all
  rw [h1, h2] at h
  have hx : (g : Matrix (Fin 4) (Fin 4) F) i 3 = ω * (g : Matrix (Fin 4) (Fin 4) F) i 3 := by
    simpa using h
  have hzero : ((1 : F) - ω) * (g : Matrix (Fin 4) (Fin 4) F) i 3 = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr hx
  rcases mul_eq_zero.mp hzero with h0 | h0
  · exact absurd h0 (sub_ne_zero.mpr (Ne.symm hω1))
  · exact h0

private theorem k328r6s_entry_3' {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (g : GL (Fin 4) F) (hg : g * z₀ = z₀ * g) (i : Fin 4) (hi : i.val < 3) :
    (g : Matrix (Fin 4) (Fin 4) F) 3 i = 0 := by
  have hω1 : ω ≠ 1 := k328r6s_omega_ne_one hF ω hω
  have hmul : (g : Matrix (Fin 4) (Fin 4) F) * (z₀ : Matrix (Fin 4) (Fin 4) F) =
      (z₀ : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) :=
    congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) hg
  have h := congrFun (congrFun hmul 3) i
  rw [hz, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h1 : (![ω, ω, ω, 1] : Fin 4 → F) 3 = 1 := by simp
  have h2 : (![ω, ω, ω, 1] : Fin 4 → F) i = ω := by
    fin_cases i <;> simp_all
  rw [h1, h2] at h
  have hx : (g : Matrix (Fin 4) (Fin 4) F) 3 i = ω * (g : Matrix (Fin 4) (Fin 4) F) 3 i := by
    simpa [mul_comm] using h.symm
  have hzero : ((1 : F) - ω) * (g : Matrix (Fin 4) (Fin 4) F) 3 i = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr hx
  rcases mul_eq_zero.mp hzero with h0 | h0
  · exact absurd h0 (sub_ne_zero.mpr (Ne.symm hω1))
  · exact h0

private theorem k328r6s_shape {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (g : GL (Fin 4) F) (hg : g * z₀ = z₀ * g) :
    (g : Matrix (Fin 4) (Fin 4) F) 0 3 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) F) 1 3 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) F) 2 3 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) F) 3 0 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) F) 3 1 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) F) 3 2 = 0 :=
  ⟨k328r6s_entry_3 hF ω hω z₀ hz g hg 0 (by norm_num),
    k328r6s_entry_3 hF ω hω z₀ hz g hg 1 (by norm_num),
    k328r6s_entry_3 hF ω hω z₀ hz g hg 2 (by norm_num),
    k328r6s_entry_3' hF ω hω z₀ hz g hg 0 (by norm_num),
    k328r6s_entry_3' hF ω hω z₀ hz g hg 1 (by norm_num),
    k328r6s_entry_3' hF ω hω z₀ hz g hg 2 (by norm_num)⟩

private theorem k328r6s_mul_33 {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (g h : GL (Fin 4) F) (hg : g ∈ k328r6s_C F z₀) (_hh : h ∈ k328r6s_C F z₀) :
    ((g * h : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3 =
      (g : Matrix (Fin 4) (Fin 4) F) 3 3 * (h : Matrix (Fin 4) (Fin 4) F) 3 3 := by
  rw [Units.val_mul, Matrix.mul_apply]
  exact Finset.sum_eq_single 3 (fun k _ hk => by
    have hk' : k.val < 3 := by
      have : k.val ≠ 3 := fun h => hk (Fin.ext h)
      omega
    rw [k328r6s_entry_3' hF ω hω z₀ hz g (k328r6s_comm_of_mem_C z₀ hg) k hk', zero_mul])
    (fun h => absurd (Finset.mem_univ 3) h)

private theorem k328r6s_d33_ne_zero {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (g : GL (Fin 4) F) (hg : g ∈ k328r6s_C F z₀) :
    (g : Matrix (Fin 4) (Fin 4) F) 3 3 ≠ 0 := by
  intro hd
  have hg' : g⁻¹ ∈ k328r6s_C F z₀ := (k328r6s_C F z₀).inv_mem hg
  have hmul := k328r6s_mul_33 hF ω hω z₀ hz g g⁻¹ hg hg'
  have h1 : ((g * g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3 = 1 := by
    rw [mul_inv_cancel]; simp
  rw [h1, hd, zero_mul] at hmul
  exact one_ne_zero hmul

private noncomputable def k328r6s_phi {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    ↥(k328r6s_C F z₀) →* Fˣ where
  toFun g := Units.mk0 (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3)
    (k328r6s_d33_ne_zero hF ω hω z₀ hz (g : GL (Fin 4) F) g.2)
  map_one' := by
    apply Units.ext
    rw [Units.val_mk0, Units.val_one]
    simp
  map_mul' g h := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
    exact k328r6s_mul_33 hF ω hω z₀ hz (g : GL (Fin 4) F) (h : GL (Fin 4) F) g.2 h.2

private theorem k328r6s_mem_Y_of_diag_one {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (x : GL (Fin 4) F) (hxC : x ∈ k328r6s_C F z₀)
    (hx33 : (x : Matrix (Fin 4) (Fin 4) F) 3 3 = 1) :
    x ∈ k328r6s_Y F := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP F 2 := k328r6s_charP hF
  have hF' : Nat.card F = (2 ^ 3) ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  let A : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j =>
    (x : Matrix (Fin 4) (Fin 4) F) (k328r6s_iota i) (k328r6s_iota j)
  have hxcomm := k328r6s_comm_of_mem_C z₀ hxC
  obtain ⟨h03, h13, h23, h30, h31, h32⟩ := k328r6s_shape hF ω hω z₀ hz x hxcomm
  have hxinf : x ∈ StatedSU 4 8 F := (Subgroup.mem_inf.mp hxC).1
  have hx_eq : (x : Matrix (Fin 4) (Fin 4) F) = blkMat k328r6s_iota A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, k328r6s_iota, blkMat, selL, Matrix.mul_apply, Matrix.add_apply,
        Matrix.sub_apply, Matrix.one_apply, Matrix.transpose_apply,
        Fin.sum_univ_three, hx33, h03, h13, h23, h30, h31, h32]
  have hunit : x ∈ CFSG.LieType.Universal.Unitary.SUid
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 3) 4 := by
    rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF' 4]
    exact hxinf
  have hxcond := (CFSG.LieType.Universal.Unitary.mem_SUid).mp hunit
  have hdetA : A.det = 1 := by
    have h1 : (blkMat k328r6s_iota A).det = 1 := by rw [← hx_eq]; exact hxcond.1
    rwa [det_blkMat k328r6s_iota_injective] at h1
  have hisoA : CFSG.LieType.Universal.Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 3) A * A = 1 := by
    have h2 : CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 3) (blkMat k328r6s_iota A) *
        blkMat k328r6s_iota A = 1 := by
      rw [← hx_eq]; exact hxcond.2
    have h2' : blkMat k328r6s_iota (CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 3) A * A) = blkMat k328r6s_iota 1 := by
      rw [conjTr_blkMat, ← blkMat_mul k328r6s_iota_injective] at h2
      rw [← blkMat_one] at h2
      exact h2
    exact blkMat_injective k328r6s_iota_injective h2'
  let Aunit : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdetA]; norm_num)
  have hAunit_coe : (Aunit : Matrix (Fin 3) (Fin 3) F) = A := rfl
  have hA1 : Aunit ∈ StatedSU 3 8 F := by
    have hmem : Aunit ∈ CFSG.LieType.Universal.Unitary.SUid
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 3) 3 :=
      (CFSG.LieType.Universal.Unitary.mem_SUid).mpr
        ⟨by rw [hAunit_coe]; exact hdetA, by rw [hAunit_coe]; exact hisoA⟩
    rwa [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF' 3] at hmem
  refine Subgroup.mem_map.mpr ⟨Aunit, hA1, ?_⟩
  apply Units.ext
  rw [coe_blkGL, hAunit_coe, hx_eq]

private theorem k328r6s_stdComp_le_Y {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    stdComp (StatedSU 4 8 F) z₀ ≤ k328r6s_Y F := by
  rw [stdComp, Subgroup.commutator_le]
  intro g hg h hh
  have hghC : ⁅g, h⁆ ∈ k328r6s_C F z₀ := by
    rw [commutatorElement_def]
    exact (k328r6s_C F z₀).mul_mem ((k328r6s_C F z₀).mul_mem
      ((k328r6s_C F z₀).mul_mem hg hh) ((k328r6s_C F z₀).inv_mem hg))
      ((k328r6s_C F z₀).inv_mem hh)
  have hgh33 : ((⁅g, h⁆ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3 = 1 := by
    have habel : ⁅k328r6s_phi hF ω hω z₀ hz ⟨g, hg⟩,
        k328r6s_phi hF ω hω z₀ hz ⟨h, hh⟩⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    have h1 : k328r6s_phi hF ω hω z₀ hz ⟨⁅g, h⁆, hghC⟩ = 1 := by
      have heq : (⟨⁅g, h⁆, hghC⟩ : ↥(k328r6s_C F z₀)) =
          ⁅(⟨g, hg⟩ : ↥(k328r6s_C F z₀)), (⟨h, hh⟩ : ↥(k328r6s_C F z₀))⁆ :=
        Subtype.ext rfl
      rw [heq, map_commutatorElement, habel]
    have h2 := congrArg (fun u : Fˣ => (u : F)) h1
    simpa [k328r6s_phi, Units.val_mk0] using h2
  exact k328r6s_mem_Y_of_diag_one hF ω hω z₀ hz ⁅g, h⁆ hghC hgh33

private theorem k328r6s_card_Y {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) : Nat.card (k328r6s_Y F) = 16547328 := by
  have hsu : Nat.card (StatedSU 3 8 F) = 16547328 := by
    have h := CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq (K := F) (q := 8)
      (by rw [Nat.card_eq_fintype_card, hF]; norm_num)
    norm_num at h
    exact h
  have hinj : Function.Injective (blkGL (F := F) (ι := k328r6s_iota) k328r6s_iota_injective) := by
    intro A B hAB
    have h1 : blkMat k328r6s_iota (A : Matrix (Fin 3) (Fin 3) F) =
        blkMat k328r6s_iota (B : Matrix (Fin 3) (Fin 3) F) := by
      have hthis := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) hAB
      rwa [coe_blkGL, coe_blkGL] at hthis
    exact Units.ext (blkMat_injective k328r6s_iota_injective h1)
  rw [k328r6s_Y, Subgroup.card_map_of_injective hinj, hsu]

private theorem k328r6s_stdComp_dvd {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    Nat.card (stdComp (StatedSU 4 8 F) z₀) ∣ 16547328 := by
  have hle := Subgroup.card_dvd_of_le (k328r6s_stdComp_le_Y hF ω hω z₀ hz)
  rwa [k328r6s_card_Y hF] at hle

private theorem k328r6s_card_X {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (_hF : Fintype.card F = 64) (z₀ : GL (Fin 4) F) (hz₀ : z₀ ∈ StatedSU 4 8 F)
    (X : Subgroup (GL (Fin 4) F)) (hXH : X ≤ StatedSU 4 8 F)
    (hpos : Pos ↥(StatedSU 4 8 F) (Subgroup.zpowers (⟨z₀, hz₀⟩ : StatedSU 4 8 F))
      (X.subgroupOf (StatedSU 4 8 F))) :
    Nat.card X = 60480 ∨ Nat.card X = 16547328 := by
  obtain ⟨hZcard, hZX, hXC, hsub, hqs, hcen, hlie⟩ := hpos
  have hcard_split : Nat.card ↥(X.subgroupOf (StatedSU 4 8 F)) =
      Nat.card (↥(X.subgroupOf (StatedSU 4 8 F)) ⧸
        Subgroup.center ↥(X.subgroupOf (StatedSU 4 8 F))) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, hcen]
  have hcardX : Nat.card X = Nat.card ↥(X.subgroupOf (StatedSU 4 8 F)) :=
    (card_subgroupOf_of_le hXH).symm
  have hquot : Nat.card (↥(X.subgroupOf (StatedSU 4 8 F)) ⧸
      Subgroup.center ↥(X.subgroupOf (StatedSU 4 8 F))) = 20160 ∨
      Nat.card (↥(X.subgroupOf (StatedSU 4 8 F)) ⧸
        Subgroup.center ↥(X.subgroupOf (StatedSU 4 8 F))) = 5515776 := by
    rcases hlie with h | h
    · left
      exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four
        (h.statedClassicalModel_of_ne_zero (by norm_num))
    · right
      exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
        (h.statedClassicalModel_of_ne_zero (by norm_num))
  rcases hquot with h | h
  · left; rw [hcardX, hcard_split, h]
  · right; rw [hcardX, hcard_split, h]

theorem row6_size (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    SizeLeaf (StatedSU 4 8 F) z₀ := by
  have _ht := ht
  intro hz₀ X hXle hpos
  have hXH : X ≤ StatedSU 4 8 F := hXle.trans (stdComp_le (StatedSU 4 8 F) z₀)
  have hcases := k328r6s_card_X hF z₀ hz₀ X hXH hpos
  have hdvdX : Nat.card X ∣ Nat.card (stdComp (StatedSU 4 8 F) z₀) :=
    Subgroup.card_dvd_of_le hXle
  have hdvdStd : Nat.card (stdComp (StatedSU 4 8 F) z₀) ∣ 16547328 :=
    k328r6s_stdComp_dvd hF ω hω z₀ hz
  rcases hcases with h | h
  · exfalso
    rw [h] at hdvdX
    exact (by norm_num : ¬ (60480 : ℕ) ∣ 16547328) (hdvdX.trans hdvdStd)
  · rw [h]
    exact Nat.dvd_antisymm (by rwa [h] at hdvdX) hdvdStd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
