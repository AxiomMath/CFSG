module

public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataWeyl
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp
import Mathlib.Tactic.Group
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusClass
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Global
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNeighbour
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Quasithin.Background.A1cTransfer
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
import CFSG.RankThree.PartOne.AUTSL.Rows
import CFSG.RankThree.PartOne.AUTSL.SylowTrick
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.S12.Sec1511Y1
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.HN.CertificateBase
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.Sporadic.Schreier.LyChain11
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType

open CFSG.SeitzReduction CFSG.SeitzReduction.OmegaPilot CFSG.SeitzReduction.SymplecticPilot
open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap
open CFSG.Assembly.LowTwoRank (StatedSp StatedOmega)
open CFSG.Open
open scoped Matrix

variable {K : Type} [Field K] {m p : ℕ} {b c : K} {ζ : Kˣ}

theorem omMinusTorusGL_injective [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Function.Injective (omMinusTorusGL (K := K) (m := m) hζ) := by
  intro f g hfg
  funext i
  have h := congrArg (fun w : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K =>
    (w : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
      (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) (Sum.inl i) (Sum.inl i)) hfg
  simp only [omMinusTorusGL_apply, kOmMDiag_coe, Matrix.diagonal_apply_eq, kOmMWeight_inl] at h
  have h1 : TableBSymp.zmodPowHom hζ (f i) = TableBSymp.zmodPowHom hζ (g i) := Units.ext h
  have h2 : TableBSymp.zmodPowHom hζ (f i * (g i)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := (TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp h2
  exact mul_inv_eq_one.mp h3

private abbrev V2 : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private abbrev e2 : V2 → K := Pi.single (Sum.inl 0) (1 : K)
private abbrev f2 : V2 → K := Pi.single (Sum.inr (Sum.inl 0)) (1 : K)
private abbrev z2 : V2 → K := Pi.single (Sum.inr (Sum.inr 0)) (1 : K)
private abbrev w2 : V2 → K := Pi.single (Sum.inr (Sum.inr 1)) (1 : K)
private abbrev u2 : V2 → K := e2 + f2 + z2

private noncomputable abbrev Q2 (b c : K) : QuadraticForm K (V2 → K) :=
  CFSG.LieType.Universal.Spin.quadMinus 2 K b c

private noncomputable abbrev flipLin (b c : K) : (V2 → K) ≃ₗ[K] (V2 → K) :=
  eichler (Q2 b c) u2 z2

private theorem Q2_z2 : Q2 (K := K) b c z2 = 1 := by
  rw [Q2, CFSG.LieType.Universal.Spin.coe_quadMinus]
  exact kOmM_statedQuadMinus_vec K b c

private theorem Q2_u [CharP K 2] (b c : K) : Q2 b c u2 = 0 := by
  rw [Q2, CFSG.LieType.Universal.Spin.quadMinus_apply]
  simp [u2, e2, f2, z2, Pi.add_apply, CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]

private theorem polar_u_z [CharP K 2] (b c : K) : polar (Q2 b c) u2 z2 = 0 := by
  rw [Q2, CFSG.LieType.Universal.Spin.polar_quadMinus]
  simp [u2, e2, f2, z2, Pi.add_apply, CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]

private theorem polar_e2 (b c : K) (y : V2 → K) :
    polar (Q2 b c) e2 y = y (Sum.inr (Sum.inl 0)) :=
  polar_single_inl_quadMinus 0 y

private theorem polar_f2 (b c : K) (y : V2 → K) :
    polar (Q2 b c) f2 y = y (Sum.inl 0) :=
  polar_single_inr_quadMinus 0 y

private theorem polar_z2 [CharP K 2] (b c : K) (y : V2 → K) :
    polar (Q2 b c) z2 y = b * y (Sum.inr (Sum.inr 1)) := by
  rw [polar_comm, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_zero]
  simp [CharTwo.two_eq_zero]

private theorem polar_w2 [CharP K 2] (b c : K) (y : V2 → K) :
    polar (Q2 b c) w2 y = b * y (Sum.inr (Sum.inr 0)) := by
  rw [polar_comm, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_one]
  simp [CharTwo.two_eq_zero]

private theorem flip_e2 [CharP K 2] (b c : K) : flipLin b c e2 = f2 := by
  rw [flipLin, eichler_apply (Q2_u b c) (polar_u_z b c)]
  have h1 : polar (Q2 b c) e2 u2 = 1 := by rw [polar_e2]; simp [u2, e2, f2, z2]
  have h2 : polar (Q2 b c) e2 z2 = 0 := by rw [polar_e2]; simp [z2]
  simp only [h1, h2, Q2_z2, mul_one, zero_add, one_smul]
  have hneg : ∀ v : V2 → K, -v = v := fun v => by funext j; simp [CharTwo.neg_eq]
  rw [show e2 + z2 - u2 = -f2 by rw [u2]; abel, hneg]

private theorem flip_f2 [CharP K 2] (b c : K) : flipLin b c f2 = e2 := by
  rw [flipLin, eichler_apply (Q2_u b c) (polar_u_z b c)]
  have h1 : polar (Q2 b c) f2 u2 = 1 := by rw [polar_f2]; simp [u2, e2, f2, z2]
  have h2 : polar (Q2 b c) f2 z2 = 0 := by rw [polar_f2]; simp [z2]
  simp only [h1, h2, Q2_z2, mul_one, zero_add, one_smul]
  have hneg : ∀ v : V2 → K, -v = v := fun v => by funext j; simp [CharTwo.neg_eq]
  rw [show f2 + z2 - u2 = -e2 by rw [u2]; abel, hneg]

private theorem flip_z2 [CharP K 2] (b c : K) : flipLin b c z2 = z2 := by
  rw [flipLin, eichler_apply (Q2_u b c) (polar_u_z b c)]
  have h1 : polar (Q2 b c) z2 u2 = 0 := by rw [polar_z2]; simp [u2, e2, f2, z2]
  have h2 : polar (Q2 b c) z2 z2 = 0 := by rw [polar_z2]; simp [z2]
  simp only [h1, h2, Q2_z2, mul_zero, add_zero, zero_smul, sub_zero]

private theorem flip_w2 [CharP K 2] (b c : K) : flipLin b c w2 = w2 + b • z2 := by
  rw [flipLin, eichler_apply (Q2_u b c) (polar_u_z b c)]
  have h1 : polar (Q2 b c) w2 u2 = b := by rw [polar_w2]; simp [u2, e2, f2, z2]
  have h2 : polar (Q2 b c) w2 z2 = b := by rw [polar_w2]; simp [z2]
  simp only [h1, h2, Q2_z2, one_mul, show b + b = 0 from CharTwo.add_self_eq_zero b,
    zero_smul, sub_zero]

private noncomputable def flipGL [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : StatedOmega (StatedQuadMinus 2 K b c) :=
  ⟨(toLinEquiv V2 K).symm (flipLin b c),
    (mem_statedOmega_iff_mem_elementaryGroup
      (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)
      (commutator_orthogonalGroup_quadMinus_small (Or.inl rfl) hirr)).mpr (by
        rw [MulEquiv.apply_symm_apply]
        exact eichler_mem_elementaryGroup (Q2 b c) u2 z2)⟩

private theorem flipGL_mulVec [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (v : V2 → K) :
    ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ v = flipLin b c v := by
  rw [← toLinEquiv_apply]
  rw [flipGL, MulEquiv.apply_symm_apply]

private theorem flipGL_col_e2 [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ e2 = f2 := by
  rw [flipGL_mulVec, flip_e2]

private theorem flipGL_col_f2 [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ f2 = e2 := by
  rw [flipGL_mulVec, flip_f2]

private theorem flipGL_col_z2 [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ z2 = z2 := by
  rw [flipGL_mulVec, flip_z2]

private theorem flipGL_col_w2 [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ w2 = w2 + b • z2 := by
  rw [flipGL_mulVec, flip_w2]

private theorem diag_one_mulVec (u : Kˣ) (x : V2) :
    (kOmMDiag K 1 (fun _ => u) : Matrix V2 V2 K) *ᵥ Pi.single x 1 =
      kOmMWeight K 1 (fun _ => u) x • Pi.single x 1 := by
  rw [kOmMDiag_coe]
  funext y
  rw [Matrix.mulVec_diagonal]
  by_cases h : y = x
  · subst h
    simp
  · simp [h]

private theorem flip_conj_diag_one [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (u : Kˣ) :
    (flipGL b c hirr : GL V2 K) * kOmMDiag K 1 (fun _ => u) *
        (flipGL b c hirr : GL V2 K)⁻¹ = kOmMDiag K 1 (fun _ => u⁻¹) := by
  have hmul : (flipGL b c hirr : GL V2 K) * kOmMDiag K 1 (fun _ => u) =
      kOmMDiag K 1 (fun _ => u⁻¹) * (flipGL b c hirr : GL V2 K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    apply Matrix.ext_of_mulVec_single
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rcases x with i | i | j
    · fin_cases i
      change ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ
          ((kOmMDiag K 1 (fun _ => u) : Matrix V2 V2 K) *ᵥ e2) =
        (kOmMDiag K 1 (fun _ => u⁻¹) : Matrix V2 V2 K) *ᵥ
          (((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ e2)
      rw [diag_one_mulVec, kOmMWeight_inl, Matrix.mulVec_smul, flipGL_col_e2]
      rw [diag_one_mulVec, kOmMWeight_inr_inl, inv_inv]
    · fin_cases i
      change ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ
          ((kOmMDiag K 1 (fun _ => u) : Matrix V2 V2 K) *ᵥ f2) =
        (kOmMDiag K 1 (fun _ => u⁻¹) : Matrix V2 V2 K) *ᵥ
          (((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ f2)
      rw [diag_one_mulVec, kOmMWeight_inr_inl, Matrix.mulVec_smul, flipGL_col_f2]
      rw [diag_one_mulVec, kOmMWeight_inl]
    · fin_cases j
      · change ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ
            ((kOmMDiag K 1 (fun _ => u) : Matrix V2 V2 K) *ᵥ z2) =
          (kOmMDiag K 1 (fun _ => u⁻¹) : Matrix V2 V2 K) *ᵥ
            (((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ z2)
        rw [diag_one_mulVec, kOmMWeight_inr_inr, one_smul, flipGL_col_z2]
        rw [diag_one_mulVec, kOmMWeight_inr_inr, one_smul]
      · change ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ
            ((kOmMDiag K 1 (fun _ => u) : Matrix V2 V2 K) *ᵥ w2) =
          (kOmMDiag K 1 (fun _ => u⁻¹) : Matrix V2 V2 K) *ᵥ
            (((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *ᵥ w2)
        rw [diag_one_mulVec, kOmMWeight_inr_inr, one_smul, flipGL_col_w2]
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        simp only [diag_one_mulVec, kOmMWeight_inr_inr, one_smul]
  rw [hmul]
  group

private abbrev Ibig (m : ℕ) : Type := Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2

private theorem weight_longEmb (t : Fin m → Kˣ) (l : Fin m) (x : V2) :
    kOmMWeight K m t (kOmMLongEmb m l x) = kOmMWeight K 1 (fun _ => t l) x := by
  rcases x with i | i | j
  · fin_cases i
    rfl
  · fin_cases i
    rfl
  · fin_cases j
    · rfl
    · rfl

private theorem weight_update_of_not_mem_range (t : Fin m → Kˣ) (l : Fin m)
    {a : Ibig m} (ha : a ∉ Set.range (kOmMLongEmb m l)) :
    kOmMWeight K m (Function.update t l (t l)⁻¹) a = kOmMWeight K m t a := by
  rcases a with i | i | j
  · have hi : i ≠ l := fun h => ha ⟨Sum.inl 0, by rw [h]; rfl⟩
    rw [kOmMWeight_inl, kOmMWeight_inl, Function.update_of_ne hi]
  · have hi : i ≠ l := fun h => ha ⟨Sum.inr (Sum.inl 0), by rw [h]; rfl⟩
    rw [kOmMWeight_inr_inl, kOmMWeight_inr_inl, Function.update_of_ne hi]
  · exact absurd ⟨Sum.inr (Sum.inr j), rfl⟩ ha

private theorem flip_conj_kOmMDiag [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (l : Fin m) (t : Fin m → Kˣ) :
    F4Pilot.coordEmbedGL (kOmMLongEmb m l) (kOmMLongEmb_injective l) (flipGL b c hirr) *
        kOmMDiag K m t *
        (F4Pilot.coordEmbedGL (kOmMLongEmb m l) (kOmMLongEmb_injective l)
          (flipGL b c hirr))⁻¹ =
      kOmMDiag K m (Function.update t l (t l)⁻¹) := by
  have hsmallGL : (flipGL b c hirr : GL V2 K) * kOmMDiag K 1 (fun _ => t l) =
      kOmMDiag K 1 (fun _ => (t l)⁻¹) * (flipGL b c hirr : GL V2 K) := by
    have h := flip_conj_diag_one b c hirr (t l)
    calc (flipGL b c hirr : GL V2 K) * kOmMDiag K 1 (fun _ => t l)
        = ((flipGL b c hirr : GL V2 K) * kOmMDiag K 1 (fun _ => t l) *
            (flipGL b c hirr : GL V2 K)⁻¹) * (flipGL b c hirr : GL V2 K) := by group
      _ = kOmMDiag K 1 (fun _ => (t l)⁻¹) * (flipGL b c hirr : GL V2 K) := by rw [h]
  have hsmall : ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) *
      (kOmMDiag K 1 (fun _ => t l) : Matrix V2 V2 K) =
      (kOmMDiag K 1 (fun _ => (t l)⁻¹) : Matrix V2 V2 K) *
        ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) := by
    simpa only [Units.val_mul] using congrArg Units.val hsmallGL
  have hentry : ∀ x y : V2, ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) x y *
      kOmMWeight K 1 (fun _ => t l) y =
      kOmMWeight K 1 (fun _ => (t l)⁻¹) x *
        ((flipGL b c hirr : GL V2 K) : Matrix V2 V2 K) x y := by
    intro x y
    have h := congrFun (congrFun hsmall x) y
    simpa only [kOmMDiag_coe, Matrix.mul_diagonal, Matrix.diagonal_mul] using h
  have hmul : (F4Pilot.coordEmbedGL (kOmMLongEmb m l) (kOmMLongEmb_injective l)
        (flipGL b c hirr) : GL (Ibig m) K) * kOmMDiag K m t =
      kOmMDiag K m (Function.update t l (t l)⁻¹) *
        (F4Pilot.coordEmbedGL (kOmMLongEmb m l) (kOmMLongEmb_injective l)
          (flipGL b c hirr) : GL (Ibig m) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, F4Pilot.coe_coordEmbedGL, kOmMDiag_coe, kOmMDiag_coe]
    apply Matrix.ext
    intro a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases ha : a ∈ Set.range (kOmMLongEmb m l)
    · obtain ⟨x, rfl⟩ := ha
      by_cases hb : b ∈ Set.range (kOmMLongEmb m l)
      · obtain ⟨y, rfl⟩ := hb
        rw [F4Pilot.coordEmbedMat_apply_image (kOmMLongEmb_injective l),
          weight_longEmb, weight_longEmb, Function.update_self]
        exact hentry x y
      · have hne : kOmMLongEmb m l x ≠ b := fun h => hb (h ▸ ⟨x, rfl⟩)
        rw [F4Pilot.coordEmbedMat_apply_of_not_mem _ (fun h => hb h.2),
          Matrix.one_apply_ne hne, zero_mul, mul_zero]
    · by_cases hb : b ∈ Set.range (kOmMLongEmb m l)
      · have hne : a ≠ b := fun h => ha (h ▸ hb)
        rw [F4Pilot.coordEmbedMat_apply_of_not_mem _ (fun h => ha h.1),
          Matrix.one_apply_ne hne, zero_mul, mul_zero]
      · rw [F4Pilot.coordEmbedMat_apply_of_not_mem _ (fun h => ha h.1)]
        by_cases hab : a = b
        · subst hab
          rw [Matrix.one_apply_eq, one_mul, mul_one, weight_update_of_not_mem_range t l ha]
        · rw [Matrix.one_apply_ne hab, zero_mul, mul_zero]
  rw [hmul]
  group

private theorem update_omMinusTorusParam (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) (l : Fin m) :
    Function.update (omMinusTorusParam m hζ f) l ((omMinusTorusParam m hζ f l)⁻¹) =
      omMinusTorusParam m hζ (Function.update f l (f l)⁻¹) := by
  funext j
  by_cases hj : j = l
  · subst hj
    simp only [Function.update_self, omMinusTorusParam_apply, map_inv]
  · simp only [Function.update_of_ne hj, omMinusTorusParam_apply]

theorem exists_sgn_mem_omMinusLongBlock [Finite K] [CharP K 2]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (l : Fin m) :
    ∃ w ∈ omMinusLongBlock K b c l, ∀ f : Fin m → Multiplicative (ZMod p),
      w * omMinusTorusGL hζ f * w⁻¹ = omMinusTorusGL hζ (SpCoord.sgnAut l f) := by
  refine ⟨F4Pilot.coordEmbedGL (kOmMLongEmb m l) (kOmMLongEmb_injective l) (flipGL b c hirr),
    Subgroup.mem_map_of_mem _ (flipGL b c hirr).2, fun f => ?_⟩
  rw [omMinusTorusGL_apply, omMinusTorusGL_apply,
    flip_conj_kOmMDiag b c hirr l (omMinusTorusParam m hζ f), SpCoord.sgnAut_apply,
    update_omMinusTorusParam]

theorem exists_swap_mem_omMinusShortBlock [CharP K 2] (hζ : ζ ^ p = 1) (i j : Fin m) :
    ∃ w ∈ omMinusShortBlock K i j, ∀ f : Fin m → Multiplicative (ZMod p),
      w * omMinusTorusGL hζ f * w⁻¹ =
        omMinusTorusGL hζ (SpCoord.permAut (Equiv.swap i j) f) := by
  refine ⟨F4Pilot.coordEmbedGL (kOmMEmb m) kOmMEmb_injective
    ((permSp K (Equiv.swap i j) : StatedSp m K) : GL (Fin m ⊕ Fin m) K),
    Subgroup.mem_map_of_mem _ (permSp_swap_mem_siegelBlockGL i j), fun f => ?_⟩
  have hcomp : (omMinusTorusParam m hζ f) ∘ ⇑(Equiv.swap i j) =
      omMinusTorusParam m hζ (SpCoord.permAut (Equiv.swap i j) f) := by
    funext k
    rw [Function.comp_apply, omMinusTorusParam_apply, omMinusTorusParam_apply,
      SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv]
  rw [omMinusTorusGL_apply, omMinusTorusGL_apply,
    ← kOmM_coordEmbedGL_diagOmega (t := omMinusTorusParam m hζ f),
    ← kOmM_coordEmbedGL_diagOmega
      (t := omMinusTorusParam m hζ (SpCoord.permAut (Equiv.swap i j) f)),
    ← map_inv, ← map_mul, ← map_mul, permSp_swap_mul_diagOmega_mul_inv, hcomp]


open Multiplicative Matrix in
theorem isSignedPerm_of_conj_omMinusTorusGL
    {F : Type} [Field F] {m p : ℕ} {ζ : Fˣ}
    (hp : p.Prime) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (g : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) F)
    (a : MulAut (Fin m → Multiplicative (ZMod p)))
    (ha : ∀ u, g * omMinusTorusGL hζ u * g⁻¹ = omMinusTorusGL hζ (a u)) :
    SpCoord.IsSignedPerm a := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hχ := ReflSp.zmodPowHom_injective hζ hζo
  have hχ1 : TableBSymp.zmodPowHom hζ (ofAdd (1 : ZMod p)) = ζ := by
    simpa only [Nat.cast_one, pow_one] using TableBSymp.zmodPowHom_natCast hζ 1
  have hdiag (u : Fin m → Multiplicative (ZMod p))
      {x y : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2}
      (hxy : (g : Matrix _ _ F) y x ≠ 0) :
      kOmMWeight F m (omMinusTorusParam m hζ u) x =
        kOmMWeight F m (omMinusTorusParam m hζ (a u)) y := by
    have hm : g * omMinusTorusGL hζ u = omMinusTorusGL hζ (a u) * g := by
      rw [← ha u]
      group
    have hm' := congrArg (fun z : GL
      (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) F =>
        (z : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
          (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) F)) hm
    simp only [Units.val_mul, omMinusTorusGL_apply, kOmMDiag_coe] at hm'
    have he := congrArg (fun z : Matrix _ _ F => z y x) hm'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    exact mul_left_cancel₀ hxy (he.trans (mul_comm _ _))
  have key (i : Fin m) : ∃ (j : Fin m) (ε : ZMod p), (ε = 1 ∨ ε = -1) ∧
      ∀ u : Fin m → Multiplicative (ZMod p), toAdd (a u j) = ε * toAdd (u i) := by
    obtain ⟨y, hy⟩ := ReflSp.exists_ne_zero_col g (Sum.inl i)
    rcases y with j | j | j
    · refine ⟨j, 1, Or.inl rfl, fun u => ?_⟩
      have he := hdiag u hy
      simp only [kOmMWeight_inl, omMinusTorusParam_apply] at he
      have h := hχ (Units.ext he)
      rw [← h, one_mul]
    · refine ⟨j, -1, Or.inr rfl, fun u => ?_⟩
      have he := hdiag u hy
      simp only [kOmMWeight_inl, kOmMWeight_inr_inl, omMinusTorusParam_apply] at he
      have he' : TableBSymp.zmodPowHom hζ (u i) =
          (TableBSymp.zmodPowHom hζ (a u j))⁻¹ := Units.ext he
      have hpw : TableBSymp.zmodPowHom hζ (u i * a u j) = 1 := by
        rw [map_mul, he']
        exact inv_mul_cancel _
      have hm : u i * a u j = 1 := (TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp hpw
      have h : a u j = (u i)⁻¹ := by
        calc
          a u j = (u i)⁻¹ * (u i * a u j) := (inv_mul_cancel_left _ _).symm
          _ = (u i)⁻¹ := by rw [hm, mul_one]
      calc
        toAdd (a u j) = -toAdd (u i) := by rw [h]; rfl
        _ = -1 * toAdd (u i) := (_root_.neg_one_mul _).symm
    · exfalso
      have he := hdiag (Pi.mulSingle i (ofAdd (1 : ZMod p))) hy
      simp only [kOmMWeight_inl, kOmMWeight_inr_inr, omMinusTorusParam_apply,
        Pi.mulSingle_eq_same, hχ1] at he
      have hζ1 : ζ = 1 := Units.ext he
      exact hp.one_lt.ne' (by rw [← hζo, hζ1, orderOf_one])
  choose j ε hε hj using key
  have hjinj : Function.Injective j := by
    intro i i' hii'
    by_contra hne
    have h1 := hj i (Pi.mulSingle i (ofAdd (1 : ZMod p)))
    have h3 := hj i' (Pi.mulSingle i (ofAdd (1 : ZMod p)))
    rw [SpCoord.toAdd_mulSingle i i 1, if_pos rfl, mul_one] at h1
    rw [SpCoord.toAdd_mulSingle i i' 1, if_neg (Ne.symm hne), mul_zero] at h3
    rw [← hii'] at h3
    have h2 : ε i = 0 := h1.symm.trans h3
    rcases hε i with hh | hh
    · rw [hh] at h2
      exact (one_ne_zero : (1 : ZMod p) ≠ 0) h2
    · rw [hh] at h2
      exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0) h2
  exact ⟨Equiv.ofBijective j hjinj.bijective_of_finite, ε, hε, fun u i => hj i u⟩


end CFSG.StandardType

end
