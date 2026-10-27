module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.GroupTheory.GL52.SylowThirtyOne
import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowOverlap
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutFacts
import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenFactor
import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B1MoreElevenD
import CFSG.Quasithin.Background.B1MoreElevenF
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.HN.CertificateBase
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyChain11
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.StandardType.GGHalf
open Matrix

@[expose] def e6TwoT31SL : Matrix.SpecialLinearGroup (Fin 6) (ZMod 2) :=
  ⟨!![0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1], by decide +kernel⟩

private theorem e6TwoT31SL_mulVec_single_4 :
    (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single (4 : Fin 6) 1 =
      Pi.single (0 : Fin 6) 1 + Pi.single (2 : Fin 6) 1 := by
  decide +kernel

private theorem e6TwoT31SL_mulVec_single_5 :
    (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single (5 : Fin 6) 1 =
      Pi.single (5 : Fin 6) 1 := by
  decide +kernel

private theorem e6TwoT31SL_pow_1_single_0 :
    (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 1 *ᵥ Pi.single (0 : Fin 6) 1 =
      Pi.single (1 : Fin 6) 1 := by
  decide +kernel

private theorem e6TwoT31SL_pow_2_single_0 :
    (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 2 *ᵥ Pi.single (0 : Fin 6) 1 =
      Pi.single (2 : Fin 6) 1 := by
  decide +kernel

private theorem e6TwoT31SL_pow_3_single_0 :
    (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 3 *ᵥ Pi.single (0 : Fin 6) 1 =
      Pi.single (3 : Fin 6) 1 := by
  decide +kernel

private theorem e6TwoT31SL_pow_4_single_0 :
    (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 4 *ᵥ Pi.single (0 : Fin 6) 1 =
      Pi.single (4 : Fin 6) 1 := by
  decide +kernel

private theorem e6TwoT31SL_fixed (w : Fin 6 → ZMod 2)
    (hw : (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w = w) :
    w = Pi.single (5 : Fin 6) (w 5) := by
  have h : ∀ w : Fin 6 → ZMod 2,
      (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w = w →
        w = Pi.single (5 : Fin 6) (w 5) := by
    decide +kernel
  exact h w hw

private theorem e6TwoT31SL_annihilate (w : Fin 6 → ZMod 2)
    (hw : (((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 5 +
      (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 2 + 1) *ᵥ w = 0)) :
    w 5 = 0 := by
  have h : ∀ w : Fin 6 → ZMod 2,
      (((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 5 +
        (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 2 + 1) *ᵥ w = 0) →
          w 5 = 0 := by
    decide +kernel
  exact h w hw

private theorem e6TwoT31SL_pow_31 : e6TwoT31SL ^ 31 = 1 := by
  decide +kernel

private theorem e6TwoT31SL_ne_one : e6TwoT31SL ≠ 1 := by
  decide +kernel

private theorem e6TwoT31SL_orderOf : orderOf e6TwoT31SL = 31 := by
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  exact orderOf_eq_prime e6TwoT31SL_pow_31 e6TwoT31SL_ne_one

private theorem e6TwoT31SL_mulVec_pow
    (A : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (hA : A * (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) * A)
    (k : ℕ) (v : Fin 6 → ZMod 2) :
    Matrix.mulVec A (Matrix.mulVec ((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ k) v) =
      Matrix.mulVec ((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ k) (Matrix.mulVec A v) := by
  let M : Matrix (Fin 6) (Fin 6) (ZMod 2) := (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2))
  have hA' : A * M = M * A := hA
  change Matrix.mulVec A (Matrix.mulVec (M ^ k) v) =
    Matrix.mulVec (M ^ k) (Matrix.mulVec A v)
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    calc Matrix.mulVec A (Matrix.mulVec (M ^ k * M) v)
        = Matrix.mulVec A (Matrix.mulVec (M ^ k) (Matrix.mulVec M v)) := by
            congr 1
            exact (Matrix.mulVec_mulVec v (M ^ k) M).symm
      _ = Matrix.mulVec (M ^ k) (Matrix.mulVec A (Matrix.mulVec M v)) := ih _
      _ = Matrix.mulVec (M ^ k) (Matrix.mulVec (A * M) v) := by
            congr 1
            exact Matrix.mulVec_mulVec v A M
      _ = Matrix.mulVec (M ^ k) (Matrix.mulVec (M * A) v) := by rw [hA']
      _ = Matrix.mulVec (M ^ k) (Matrix.mulVec M (Matrix.mulVec A v)) := by
            congr 1
            exact (Matrix.mulVec_mulVec v M A).symm
      _ = Matrix.mulVec (M ^ k * M) (Matrix.mulVec A v) :=
            Matrix.mulVec_mulVec (Matrix.mulVec A v) (M ^ k) M

private theorem e6TwoT31SL_cent_matrix_comm
    (A : ↥(Subgroup.centralizer ({e6TwoT31SL} :
      Set (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2))))) :
    (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 6) (ZMod 2) =>
    (x : Matrix (Fin 6) (Fin 6) (ZMod 2)))
    (Subgroup.mem_centralizer_singleton_iff.1 A.2)
  simpa only [Matrix.SpecialLinearGroup.coe_mul] using h

private theorem e6TwoT31SL_cent_mulVec_single_5
    (A : ↥(Subgroup.centralizer ({e6TwoT31SL} :
      Set (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2))))) :
    Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (5 : Fin 6) 1) =
      Pi.single (5 : Fin 6) 1 := by
  have hcomm := e6TwoT31SL_cent_matrix_comm A
  have hw : Matrix.mulVec (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2))
      (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (5 : Fin 6) 1)) =
      Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (5 : Fin 6) 1) := by
    rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, e6TwoT31SL_mulVec_single_5]
  have hfixed := e6TwoT31SL_fixed _ hw
  have hne : Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (5 : Fin 6) 1) ≠ 0 := by
    intro hzero
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero (Matrix.SpecialLinearGroup.det_ne_zero A.1) hzero
    have := congrFun h0 (5 : Fin 6)
    simpa using this
  have h5ne : (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2))
      (Pi.single (5 : Fin 6) 1)) 5 ≠ 0 := by
    intro h5
    apply hne
    rw [hfixed, h5]
    funext i
    simp
  have h5eq : (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2))
      (Pi.single (5 : Fin 6) 1)) 5 = 1 := by
    have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hz _ with h | h
    · exact absurd h h5ne
    · exact h
  rw [hfixed, h5eq]

private theorem e6TwoT31SL_cent_mulVec_mem
    (A : ↥(Subgroup.centralizer ({e6TwoT31SL} :
      Set (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2))))) :
    (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1)) 5 = 0 ∧
      Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1) ≠ 0 := by
  have hcomm := e6TwoT31SL_cent_matrix_comm A
  have hpow := e6TwoT31SL_mulVec_pow (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) hcomm
  have hAe2 : Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (2 : Fin 6) 1) =
      Matrix.mulVec ((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 2)
        (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1)) := by
    have := hpow 2 (Pi.single (0 : Fin 6) 1)
    rwa [e6TwoT31SL_pow_2_single_0] at this
  have hAe4 : Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (4 : Fin 6) 1) =
      Matrix.mulVec ((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 4)
        (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1)) := by
    have := hpow 4 (Pi.single (0 : Fin 6) 1)
    rwa [e6TwoT31SL_pow_4_single_0] at this
  have hann : Matrix.mulVec (((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 5 +
        (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 2 + 1))
        (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1)) = 0 := by
    have h1 : Matrix.mulVec (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2))
        (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (4 : Fin 6) 1)) =
        Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2))
          (Matrix.mulVec (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (4 : Fin 6) 1)) := by
      rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec]
    have h5 : Matrix.mulVec ((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 5)
        (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1)) =
        Matrix.mulVec (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2))
          (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (4 : Fin 6) 1)) := by
      rw [hAe4]
      conv_rhs => rw [Matrix.mulVec_mulVec]
      rw [← pow_succ']
    have hAadd : Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2))
        (Matrix.mulVec (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (4 : Fin 6) 1)) =
        Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1) +
          Matrix.mulVec ((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 2)
            (Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1)) := by
      rw [e6TwoT31SL_mulVec_single_4, Matrix.mulVec_add, hAe2]
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, h5, h1, hAadd]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [CharTwo.add_cancel_right, CharTwo.add_self_eq_zero]
  exact ⟨e6TwoT31SL_annihilate _ hann, fun hzero => by
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero (Matrix.SpecialLinearGroup.det_ne_zero A.1) hzero
    have := congrFun h0 (0 : Fin 6)
    simpa using this⟩

private theorem e6TwoT31SL_cent_mulVec_injective :
    Function.Injective (fun A : ↥(Subgroup.centralizer ({e6TwoT31SL} :
      Set (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)))) =>
        Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1)) := by
  intro A A' h0
  have hcommA := e6TwoT31SL_cent_matrix_comm A
  have hcommA' := e6TwoT31SL_cent_matrix_comm A'
  have hpowA := e6TwoT31SL_mulVec_pow (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) hcommA
  have hpowA' := e6TwoT31SL_mulVec_pow (A'.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) hcommA'
  have hcolM : ∀ k : ℕ,
      Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2))
        (Matrix.mulVec ((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ k)
          (Pi.single (0 : Fin 6) 1)) =
      Matrix.mulVec (A'.1 : Matrix (Fin 6) (Fin 6) (ZMod 2))
        (Matrix.mulVec ((e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ k)
          (Pi.single (0 : Fin 6) 1)) := by
    intro k
    have h0' : Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1) =
        Matrix.mulVec (A'.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (0 : Fin 6) 1) := h0
    rw [hpowA k, hpowA' k, h0']
  have hcol1 : Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (1 : Fin 6) 1) =
      Matrix.mulVec (A'.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (1 : Fin 6) 1) := by
    have := hcolM 1
    rwa [e6TwoT31SL_pow_1_single_0] at this
  have hcol2 : Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (2 : Fin 6) 1) =
      Matrix.mulVec (A'.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (2 : Fin 6) 1) := by
    have := hcolM 2
    rwa [e6TwoT31SL_pow_2_single_0] at this
  have hcol3 : Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (3 : Fin 6) 1) =
      Matrix.mulVec (A'.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (3 : Fin 6) 1) := by
    have := hcolM 3
    rwa [e6TwoT31SL_pow_3_single_0] at this
  have hcol4 : Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (4 : Fin 6) 1) =
      Matrix.mulVec (A'.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (4 : Fin 6) 1) := by
    have := hcolM 4
    rwa [e6TwoT31SL_pow_4_single_0] at this
  have hcol5 : Matrix.mulVec (A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (5 : Fin 6) 1) =
      Matrix.mulVec (A'.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Pi.single (5 : Fin 6) 1) := by
    rw [e6TwoT31SL_cent_mulVec_single_5 A, e6TwoT31SL_cent_mulVec_single_5 A']
  ext i j
  fin_cases j
  · have := congrFun h0 i; simpa [Matrix.mulVec_single_one] using this
  · have := congrFun hcol1 i; simpa [Matrix.mulVec_single_one] using this
  · have := congrFun hcol2 i; simpa [Matrix.mulVec_single_one] using this
  · have := congrFun hcol3 i; simpa [Matrix.mulVec_single_one] using this
  · have := congrFun hcol4 i; simpa [Matrix.mulVec_single_one] using this
  · have := congrFun hcol5 i; simpa [Matrix.mulVec_single_one] using this

private theorem e6TwoT31SL_centralizer_eq :
    Subgroup.centralizer ({e6TwoT31SL} : Set (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2))) =
      Subgroup.zpowers e6TwoT31SL := by
  have hle : Subgroup.zpowers e6TwoT31SL ≤
      Subgroup.centralizer ({e6TwoT31SL} :
        Set (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2))) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hcard : Nat.card (Subgroup.centralizer ({e6TwoT31SL} :
      Set (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)))) ≤ 31 := by
    let C := Subgroup.centralizer ({e6TwoT31SL} :
      Set (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)))
    let β := {v : Fin 6 → ZMod 2 // v 5 = 0 ∧ v ≠ 0}
    let f : ↥C → β := fun A =>
      ⟨(A.1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Pi.single (0 : Fin 6) 1,
        e6TwoT31SL_cent_mulVec_mem A⟩
    have hf : Function.Injective f := by
      intro A A' h
      exact e6TwoT31SL_cent_mulVec_injective (congrArg Subtype.val h)
    calc Nat.card ↥C ≤ Nat.card β := Nat.card_le_card_of_injective f hf
      _ = 31 := by rw [Nat.card_eq_fintype_card]; decide
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, e6TwoT31SL_orderOf]
  exact hcard

private theorem e6TwoT31_map_sl_injective
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 6) f) := by
  intro A B h
  ext i j
  have h1 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 6) S =>
    (M : Matrix (Fin 6) (Fin 6) S) i j) h
  exact hf h1

private theorem e6TwoT31_card_F2 : Nat.card F2 = 2 := by
  rw [GaloisField.card 2 1 (by omega), pow_one]

@[expose] noncomputable def e6TwoT31 :
    EC :=
  E6Pilot.slToAdjointE6 F2 (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F2) e6TwoT31SL)

theorem e6TwoT31_mem_lE :
    e6TwoT31 ∈ lE := by
  unfold e6TwoT31 lE
  exact E6Pilot.slToAdjointE6_mem_a5Levi _

theorem orderOf_e6TwoT31 :
    orderOf e6TwoT31 = 31 := by
  have hinj : Function.Injective (E6Pilot.slToAdjointE6 F2) :=
    E6Pilot.injective_slToAdjointE6_two e6TwoT31_card_F2
  have hmap_inj : Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin 6) (ZMod.castHom (dvd_refl 2) F2)) :=
    e6TwoT31_map_sl_injective (ZMod.castHom (dvd_refl 2) F2).injective
  have hT31 : (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F2) e6TwoT31SL) ^ 31 =
      1 := by
    rw [← map_pow, e6TwoT31SL_pow_31, map_one]
  have hTne : (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F2) e6TwoT31SL) ≠ 1 := by
    intro h
    exact e6TwoT31SL_ne_one (hmap_inj (by rw [h, map_one]))
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hord : orderOf (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F2)
      e6TwoT31SL) = 31 :=
    orderOf_eq_prime hT31 hTne
  unfold e6TwoT31
  rw [orderOf_injective (E6Pilot.slToAdjointE6 F2) hinj]
  exact hord

theorem lE_inf_centralizer_e6TwoT31 :
    lE ⊓ Subgroup.centralizer ({e6TwoT31} : Set EC) = Subgroup.zpowers e6TwoT31 := by
  have hinj : Function.Injective (E6Pilot.slToAdjointE6 F2) :=
    E6Pilot.injective_slToAdjointE6_two e6TwoT31_card_F2
  have hrange : (E6Pilot.slToAdjointE6 F2).range = lE := E6Pilot.range_slToAdjointE6
  letI : Fintype F2 := Fintype.ofFinite F2
  have hcard : Fintype.card F2 = 2 := by
    rw [← Nat.card_eq_fintype_card]
    rw [GaloisField.card 2 1 (by omega), pow_one]
  let e : ZMod 2 ≃+* F2 := ZMod.ringEquiv (R := F2) (n := 2) hcard
  let F : Matrix.SpecialLinearGroup (Fin 6) (ZMod 2) →*
      Matrix.SpecialLinearGroup (Fin 6) F2 :=
    Matrix.SpecialLinearGroup.map (e : ZMod 2 →+* F2)
  let G : Matrix.SpecialLinearGroup (Fin 6) F2 →*
      Matrix.SpecialLinearGroup (Fin 6) (ZMod 2) :=
    Matrix.SpecialLinearGroup.map (e.symm : F2 →+* ZMod 2)
  let T' : Matrix.SpecialLinearGroup (Fin 6) F2 := F e6TwoT31SL
  have ht0 : e6TwoT31 = E6Pilot.slToAdjointE6 F2 T' := rfl
  have hcompFG : F.comp G = MonoidHom.id (Matrix.SpecialLinearGroup (Fin 6) F2) := by
    show (Matrix.SpecialLinearGroup.map (e : ZMod 2 →+* F2)).comp
        (Matrix.SpecialLinearGroup.map (e.symm : F2 →+* ZMod 2)) =
        MonoidHom.id (Matrix.SpecialLinearGroup (Fin 6) F2)
    apply MonoidHom.ext
    intro A
    apply Subtype.ext
    ext i j
    rw [MonoidHom.comp_apply, MonoidHom.id_apply,
      Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe]
    simp [Matrix.map_apply, e.apply_symm_apply]
  have hcompGF : G.comp F = MonoidHom.id (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)) := by
    show (Matrix.SpecialLinearGroup.map (e.symm : F2 →+* ZMod 2)).comp
        (Matrix.SpecialLinearGroup.map (e : ZMod 2 →+* F2)) =
        MonoidHom.id (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2))
    apply MonoidHom.ext
    intro A
    apply Subtype.ext
    ext i j
    rw [MonoidHom.comp_apply, MonoidHom.id_apply,
      Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe]
    simp [Matrix.map_apply, e.symm_apply_apply]
  have hGT' : G T' = e6TwoT31SL := by
    have := congrArg (fun f : Matrix.SpecialLinearGroup (Fin 6) (ZMod 2) →*
        Matrix.SpecialLinearGroup (Fin 6) (ZMod 2) => f e6TwoT31SL) hcompGF
    simpa [T'] using this
  have hFA : ∀ A : Matrix.SpecialLinearGroup (Fin 6) F2, F (G A) = A := by
    intro A
    have := congrArg (fun f : Matrix.SpecialLinearGroup (Fin 6) F2 →*
        Matrix.SpecialLinearGroup (Fin 6) F2 => f A) hcompFG
    simpa using this
  refine le_antisymm ?_ ?_
  · rintro d ⟨hdL, hdc⟩
    have hdc' : d * e6TwoT31 = e6TwoT31 * d := Subgroup.mem_centralizer_singleton_iff.1 hdc
    have hdran : d ∈ (E6Pilot.slToAdjointE6 F2).range := by rw [hrange]; exact hdL
    obtain ⟨A', hA'⟩ := hdran
    rw [← hA'] at hdc' ⊢
    have hcomm' : A' * T' = T' * A' := by
      apply hinj
      show E6Pilot.slToAdjointE6 F2 (A' * T') = E6Pilot.slToAdjointE6 F2 (T' * A')
      rw [map_mul, map_mul]
      rw [ht0] at hdc'
      exact hdc'
    let A : Matrix.SpecialLinearGroup (Fin 6) (ZMod 2) := G A'
    have hAcomm : A * e6TwoT31SL = e6TwoT31SL * A := by
      have := congrArg G hcomm'
      simp only [map_mul, hGT'] at this
      exact this
    have hAmem : A ∈ Subgroup.zpowers e6TwoT31SL := by
      rw [← e6TwoT31SL_centralizer_eq]
      exact Subgroup.mem_centralizer_singleton_iff.2 hAcomm
    have hA'eq : F A = A' := hFA A'
    rw [Subgroup.mem_zpowers_iff] at hAmem ⊢
    obtain ⟨k, hk⟩ := hAmem
    refine ⟨k, ?_⟩
    calc (e6TwoT31 : EC) ^ k = (E6Pilot.slToAdjointE6 F2 T') ^ k := by rw [ht0]
      _ = E6Pilot.slToAdjointE6 F2 (T' ^ k) := by rw [map_zpow]
      _ = E6Pilot.slToAdjointE6 F2 A' := by
            congr 1
            calc T' ^ k = (F e6TwoT31SL) ^ k := rfl
              _ = F (e6TwoT31SL ^ k) := by rw [map_zpow]
              _ = F A := by rw [hk]
              _ = A' := hA'eq
  · refine le_inf ?_ ?_
    · rw [Subgroup.zpowers_le]; exact e6TwoT31_mem_lE
    · rw [Subgroup.zpowers_le]; exact Subgroup.mem_centralizer_singleton_iff.2 rfl

end CFSG.StandardType.GGSixE6Two
