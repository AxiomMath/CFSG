module

public import CFSG.LocalAnalysis.StandardType.GGNbrD4TwoCenter
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGBstarDeltaEq
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanMemberOut
import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma85
import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.FischerOddCore.Basic
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2173
public import Certificates.Certificate2178
public import Certificates.Certificate2274
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83
import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

section OriginalNormalizer


theorem GGConfig.centralizer_y_le_normalizer_of_D4two_nbr_eq_center
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (hRig : GGLabelRigidInput) (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hEq : B = Bs) (hZ : Subgroup.center X ≠ ⊥) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨lab, -, -, R, _, I, F, θ, ⟨-, hN, -⟩⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  obtain ⟨rfl, hγ⟩ := hcfg.card_gamma_of_D4two_nbr hnb hRig hmark hN
  have hact : ∃ b : Bs, ggGamma X hN b ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : (ggGamma X hN).range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨b, rfl⟩
      rw [Subgroup.mem_bot, hall]
    rw [hbot, Subgroup.card_bot] at hγ
    norm_num at hγ
  obtain ⟨E, hEX, hE, hEc⟩ := OrthTorus.exists_elemAbelian_four_of_D4two_marking
    hRig hcfg.2.1.2.1 hcfg.2.1.2.2.2 hmark hN hact
  have hnc : ∃ S : Subgroup G, S ≤ X ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
    refine ⟨E, hEX, TableB.isPGroup_of_isElemAbelian hE, ?_⟩
    intro hc
    have hb := LocalAnalysis.GLTheoremA.S8.card_le_of_cyclic Nat.prime_three hE hc
    rw [hEc] at hb
    norm_num at hb
  have hSY := hcfg.sStar_of_D4two_nbr_of_eq_of_center_ne_bot hnb hRig hmark hEq hZ
  exact fun g hg => mem_normalizer_of_sstar hSY hnc hg

theorem GGConfig.original_J_component_of_D4two_nbr_eq_center_of_outer
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (hRig : GGLabelRigidInput) (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hEq : B = Bs) (hZ : Subgroup.center X ≠ ⊥)
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :
    J ≤ X ∧ IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hJC := isComponentOf_inf_centralizer_of_stdSub hS hcfg.2.2.1 hnb.2.1
  have hJY : J ≤ Subgroup.centralizer ({y} : Set G) := hJC.1.trans inf_le_left
  have hJN := hJY.trans (hcfg.centralizer_y_le_normalizer_of_D4two_nbr_eq_center
    hnb hRig hmark hEq hZ)
  have hJX : J ≤ X := le_of_ggNbr_of_normalizes_of_outer_solvable
    hcfg.1 hcfg.2.2 hnb hJN hOut
  refine ⟨hJX, LocalAnalysis.ComponentInitial.isComponentOf_of_le hJC
    (le_inf hJX (hJC.1.trans inf_le_right)) ?_⟩
  exact inf_le_inf hnb.1.2.2.2.1 le_rfl

end OriginalNormalizer

section NativeOuter


theorem GGSecFiveRouteCfg.original_J_component_of_D4two_nbr_eq_center
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (hRig : GGLabelRigidInput) (hmark : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hEq : B = Bs) (hZ : Subgroup.center X ≠ ⊥) :
    J ≤ X ∧ IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier :=
    LocalAnalysis.ComponentInitial.catalogueSchreier_iff_schreierFor.mpr
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hOS := ggSecFive_outSolvable_of_member hSch hcfg (Or.inr ⟨y, hnb⟩)
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    (CFSG.isSolvable_quotient_iff_exists_derivedSeries_le
      (CFSG.ComponentClassification.OuterAutomorphisms.inner X)).mpr hOS
  exact hcfg.1.1.original_J_component_of_D4two_nbr_eq_center_of_outer
    hnb hRig hmark hEq hZ hOut

end NativeOuter

end CFSG.StandardType

end
