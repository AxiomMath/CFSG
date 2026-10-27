module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightModel
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.GH74.Statements
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
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
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Field
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldAlign
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Quasithin.Background.A1cTransfer
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
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
import CFSG.Sporadic.Schreier.LyChain11
import CFSG.Sporadic.Schreier.TitsOther
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {F : Type} [Field F] {p : ℕ}

private theorem torusHom_eq_diagSp {n : ℕ} (t : Fin n → Fˣ) :
    torusHom t = CFSG.SeitzReduction.SymplecticPilot.diagSp F n t := by
  apply statedSp_ext
  rw [coe_torusHom, ← CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply,
    CFSG.SeitzReduction.SymplecticPilot.mat_diagSp]
  rfl

theorem spPlaneTorus_sl2Diag_comp_apply (n : ℕ)
    (χ : Multiplicative (ZMod p) →* Fˣ) (v : Fin n → Multiplicative (ZMod p)) :
    spPlaneTorus n (sl2Diag.comp χ) v =
      CFSG.SeitzReduction.SymplecticPilot.diagSp F n (fun i => χ (v i)) := by
  let c : (Fin n → Multiplicative (ZMod p)) →* (Fin n → Fˣ) :=
    MonoidHom.pi fun i => χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) i)
  have h : spPlaneTorus n (sl2Diag.comp χ) =
      (CFSG.SeitzReduction.SymplecticPilot.diagSp F n).comp c := by
    apply MonoidHom.pi_ext
    intro i a
    rw [spPlaneTorus_mulSingle]
    simp only [MonoidHom.comp_apply]
    have hcoords : c (Pi.mulSingle i a) = Pi.mulSingle i (χ a) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [c]
      · simp [c, Pi.mulSingle_eq_of_ne hj]
    rw [hcoords]
    change lam i (sl2Diag (χ a)) = _
    rw [lam_sl2Diag]
    exact torusHom_eq_diagSp _
  have hv := congrArg (fun f : (Fin n → Multiplicative (ZMod p)) →* StatedSp n F => f v) h
  have hcv : c v = fun i => χ (v i) := by
    funext i
    simp [c]
  change spPlaneTorus n (sl2Diag.comp χ) v =
    CFSG.SeitzReduction.SymplecticPilot.diagSp F n (c v) at hv
  rwa [hcv] at hv

theorem spPlaneTorus_spPlaneZetaSplit (n : ℕ) {ω : Fˣ} (hω : ω ^ p = 1) :
    spPlaneTorus n (spPlaneZetaSplit ω hω) = CFSG.StandardType.TableBSymp.spTorusSt hω := by
  apply MonoidHom.pi_ext
  intro i a
  rw [spPlaneTorus_mulSingle, CFSG.StandardType.TableBSymp.spTorusSt_eq_diagSp]
  have hcoords : (fun j => CFSG.StandardType.TableBSymp.zmodPowHom hω
        ((Pi.mulSingle i a : Fin n → Multiplicative (ZMod p)) j)) =
      Pi.mulSingle i (CFSG.StandardType.TableBSymp.zmodPowHom hω a) := by
    funext j
    by_cases h : j = i
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, map_one]
  rw [hcoords]
  have hzeta : spPlaneZetaSplit ω hω a =
      sl2Diag (CFSG.StandardType.TableBSymp.zmodPowHom hω a) := rfl
  rw [hzeta, lam_sl2Diag]
  exact torusHom_eq_diagSp _

theorem spPlaneConj_split [Finite F] [Fact p.Prime] (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) {ω : Fˣ}
    (hω1 : ω ^ p = 1) (hωo : orderOf ω = p) : SpPlaneConj F p (spPlaneZetaSplit ω hω1) := by
  intro n E hE hcard
  let S : StatedSp n F →* GL (Fin n ⊕ Fin n) F := (StatedSp n F).subtype
  have hS : Function.Injective S := Subgroup.subtype_injective (StatedSp n F)
  have hE₁ : IsElemAbelian p (E.map S) := by
    refine ⟨?_, ?_⟩
    · haveI := hE.1
      infer_instance
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [← map_pow, hE.2 y hy, map_one]
  have hcard₁ : p ^ n ≤ Nat.card (E.map S) := by
    rw [← Nat.card_congr (E.equivMapOfInjective S hS).toEquiv]
    exact hcard
  have hE₁Sp : E.map S ≤ CFSG.Assembly.LargeEvenSpGroup F n := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨P, hP, hconj⟩ :=
    CFSG.StandardType.TableBSymp.exists_conj_eq_range_spTorusGL (K := F) (m := n) (ζ := ω)
      hp2 hpF hωo hω1 hE₁Sp hE₁ hcard₁
  let c : StatedSp n F := ⟨P⁻¹, (CFSG.Assembly.LargeEvenSpGroup F n).inv_mem hP⟩
  refine ⟨c, ?_⟩
  apply Subgroup.map_injective hS
  have hcomp : S.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj P⁻¹).toMonoidHom.comp S := by
    ext x
    simp [c, S, MulAut.conj_apply, map_mul, map_inv]
  calc
    (E.map (MulAut.conj c).toMonoidHom).map S
        = E.map (S.comp (MulAut.conj c).toMonoidHom) :=
          Subgroup.map_map E S (MulAut.conj c).toMonoidHom
    _ = E.map ((MulAut.conj P⁻¹).toMonoidHom.comp S) := by rw [hcomp]
    _ = (E.map S).map (MulAut.conj P⁻¹).toMonoidHom :=
          (Subgroup.map_map E (MulAut.conj P⁻¹).toMonoidHom S).symm
    _ = (CFSG.StandardType.TableBSymp.spTorusGL (m := n) hω1).range := hconj
    _ = ((spPlaneTorus n (spPlaneZetaSplit ω hω1)).range).map S := by
          have hcomp2 : S.comp (CFSG.StandardType.TableBSymp.spTorusSt (K := F) hω1) =
              CFSG.StandardType.TableBSymp.spTorusGL (m := n) hω1 := by
            ext f
            rfl
          rw [spPlaneTorus_spPlaneZetaSplit n hω1, MonoidHom.map_range, hcomp2]

end CFSG.StandardType.SpJoin


namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag coe_sl2Diag)
open scoped MatrixGroups

theorem GGSecFiveBPermSpKFrame.toPlaneFrame
    {G : Type} [Group G] {p n r f : ℕ} {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpKFrame Bs L eta π κ χ) :
    GGSecFiveBPermSpPlaneFrame Bs L eta π κ (sl2Diag.comp χ) := by
  have hζ : Function.Injective (sl2Diag.comp χ) := by
    intro a b h
    apply hF.2.2.1
    apply Units.ext
    have hm := congrArg
      (fun A : SL(2, GaloisField 2 f) => (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 0) h
    simpa [MonoidHom.comp_apply, coe_sl2Diag] using hm
  refine ⟨hF.1, hF.2.1, hζ, ?_⟩
  intro b s
  have hT : SpJoin.spPlaneTorus (r + 1) (sl2Diag.comp χ)
        (fun m => eta b (π m.succ)) = ggSecFiveBPermSpKTorus eta π χ b := by
    dsimp only [ggSecFiveBPermSpKTorus]
    rw [SpJoin.spPlaneTorus_sl2Diag_comp_apply,
      CFSG.SeitzReduction.SymplecticPilot.diagSp_eq_equivStatedSp_diagonal]
  simpa only [hT] using hF.2.2.2 b s


end CFSG.StandardType
