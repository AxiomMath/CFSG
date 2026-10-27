module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3FinInputs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.A3StructureBasic
import CFSG.Quasithin.H13.J4Core
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
import Certificates.Certificate43

public section

open CFSG
open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A5
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

local notation "V4" => Fin 4 → ZMod 2

public section

open CFSG
open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A5
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace CertificateChecks.Batch5952

open CFSG
open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A5
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

private theorem quadHyp_single_0_check_0 : quadHyp (Pi.single 0 1 : V4) = 0 := by
  decide +kernel

private theorem quadHyp_single_1_check_1 : quadHyp (Pi.single 1 1 : V4) = 0 := by
  decide +kernel

private theorem quadHyp_single_0_1_check_2 : quadHyp ((Pi.single 0 1 : V4) + Pi.single 1 1) = 1 := by
  decide +kernel

private theorem quadHyp_single_2_check_3 : quadHyp (Pi.single 2 1 : V4) = 0 := by
  decide +kernel

private theorem quadHyp_single_0_2_check_4 : quadHyp ((Pi.single 0 1 : V4) + Pi.single 2 1) = 0 := by
  decide +kernel

private theorem quadHyp_single_1_2_check_5 : quadHyp ((Pi.single 1 1 : V4) + Pi.single 2 1) = 0 := by
  decide +kernel

private theorem quadHyp_single_3_check_6 : quadHyp (Pi.single 3 1 : V4) = 0 := by
  decide +kernel

private theorem quadHyp_single_0_3_check_7 : quadHyp ((Pi.single 0 1 : V4) + Pi.single 3 1) = 0 := by
  decide +kernel

private theorem quadHyp_single_1_3_check_8 : quadHyp ((Pi.single 1 1 : V4) + Pi.single 3 1) = 0 := by
  decide +kernel

private theorem quadHyp_single_2_3_check_9 : quadHyp ((Pi.single 2 1 : V4) + Pi.single 3 1) = 1 := by
  decide +kernel

end CertificateChecks.Batch5952

namespace Certificates

open CertificateChecks


open CFSG in
open CFSG.QuasithinUnique in
open CFSG.QuasithinUnique.A5 in
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3 in
theorem certificate5952 : (quadHyp (Pi.single 0 1 : V4) = 0)
    ∧ (quadHyp (Pi.single 1 1 : V4) = 0)
    ∧ (quadHyp ((Pi.single 0 1 : V4) + Pi.single 1 1) = 1)
    ∧ (quadHyp (Pi.single 2 1 : V4) = 0)
    ∧ (quadHyp ((Pi.single 0 1 : V4) + Pi.single 2 1) = 0)
    ∧ (quadHyp ((Pi.single 1 1 : V4) + Pi.single 2 1) = 0)
    ∧ (quadHyp (Pi.single 3 1 : V4) = 0)
    ∧ (quadHyp ((Pi.single 0 1 : V4) + Pi.single 3 1) = 0)
    ∧ (quadHyp ((Pi.single 1 1 : V4) + Pi.single 3 1) = 0)
    ∧ (quadHyp ((Pi.single 2 1 : V4) + Pi.single 3 1) = 1) := by
  exact ⟨CertificateChecks.Batch5952.quadHyp_single_0_check_0, CertificateChecks.Batch5952.quadHyp_single_1_check_1, CertificateChecks.Batch5952.quadHyp_single_0_1_check_2, CertificateChecks.Batch5952.quadHyp_single_2_check_3, CertificateChecks.Batch5952.quadHyp_single_0_2_check_4, CertificateChecks.Batch5952.quadHyp_single_1_2_check_5, CertificateChecks.Batch5952.quadHyp_single_3_check_6, CertificateChecks.Batch5952.quadHyp_single_0_3_check_7, CertificateChecks.Batch5952.quadHyp_single_1_3_check_8, CertificateChecks.Batch5952.quadHyp_single_2_3_check_9⟩

end Certificates
