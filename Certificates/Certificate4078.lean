module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M22Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Two
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM22
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Schreier.M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M22Inputs
import Certificates.Kernel.LocalQT.Core.C4078g
import Certificates.Kernel.LocalQT.Core.C4078h
import Certificates.Kernel.LocalQT.Core.C4078d
import CFSG.Certificates.Kernel.LocalQTCoreCSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43
import CFSG.Certificates.Kernel.LocalQTLatMSound
import CFSG.Certificates.Kernel.LocalQTListLemmas
import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenBundle
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCT
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
import CFSG.Monster.Code.Weights
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BCase3Base
import CFSG.Quasithin.Background.A3Structure36BCasesBase
import CFSG.Quasithin.Background.A3Structure36BCommonBase
import CFSG.Quasithin.Background.A3Structure36BFrattini
import CFSG.Quasithin.Background.A3Structure36BHeisBase
import CFSG.Quasithin.Background.A3Structure36BHomocyclic
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36BStarBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent

set_option maxRecDepth 100000

public section

namespace Certificates

private theorem injh : CFSG.KC.LQT.L.chainInj 22 CFSG.KD.LQT.C4078h.C = true := by quickRfl

private theorem injd : CFSG.KC.LQT.L.chainInj 22 CFSG.KD.LQT.C4078d.C = true := by quickRfl

open CFSG.KC.LQT.Syl CFSG.KC.LQT.L CFSG.QuasithinUnique.A5.Kc3M22Data in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.Kc3M22 in
open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six CFSG.QuasithinUnique.Unc25G2.M2x CFSG.QuasithinUnique.A5.Kc3Cert CFSG.QuasithinUnique.A5.Kc3M22Data in
theorem certificate4078 : (hexad.coreCheckT gR 443520 = true)
    ∧ (CFSG.QuasithinUnique.A5.Kc3M22Data.duad.coreCheckT gR 443520 = true)
    ∧ (hexad.hypACheck gR = true)
    ∧ (CFSG.QuasithinUnique.A5.Kc3M22Data.duad.hypACheck gR = true) := by
  have h1 : hexad.eW = CFSG.KD.LQT.C4078h.eWL := rfl
  have h2 : hexad.nW = CFSG.KD.LQT.C4078h.nWL := rfl
  have h3 : hexad.rT = CFSG.KD.LQT.C4078h.rTL := rfl
  have h4 : hexad.nOrd = 5760 := rfl
  have h5 : hexad.depth = 21 := rfl
  have d1 : duad.eW = CFSG.KD.LQT.C4078d.eWL := rfl
  have d2 : duad.nW = CFSG.KD.LQT.C4078d.nWL := rfl
  have d3 : duad.rT = CFSG.KD.LQT.C4078d.rTL := rfl
  have d4 : duad.nOrd = 1920 := rfl
  have d5 : duad.depth = 18 := rfl
  have hcl : ∀ j < 22, chainChunk 22 CFSG.KD.LQT.C4078h.C CFSG.KD.LQT.C4078h.clP j = true :=
    CFSG.KD.LQT.C4078h.clAll
  have hA : ∀ j < 22, chainChunk 22 CFSG.KD.LQT.C4078h.C CFSG.KD.LQT.C4078h.hyP j = true :=
    CFSG.KD.LQT.C4078h.hyAll
  have dcl : ∀ j < 22, chainChunk 22 CFSG.KD.LQT.C4078d.C CFSG.KD.LQT.C4078d.clP j = true :=
    CFSG.KD.LQT.C4078d.clAll
  have dA : ∀ j < 22, chainChunk 22 CFSG.KD.LQT.C4078d.C CFSG.KD.LQT.C4078d.hyP j = true :=
    CFSG.KD.LQT.C4078d.hyAll
  open CFSG.KD.LQT.C4078 in
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine coreC_sound _ hGLh hexad 443520 CFSG.KD.LQT.C4078h.C CFSG.KD.LQT.C4078h.W ?_
      CFSG.KD.LQT.C4078h.hC injh ?_ ?_ ?_ ?_ ?_ ?_
    · rw [h1]; exact CFSG.KD.LQT.C4078h.hE
    · rw [h2]; exact CFSG.KD.LQT.C4078h.hg
    · rw [h2, h5]; exact CFSG.KD.LQT.C4078h.hw
    · rw [h2]; exact hcl
    · rw [h4]; exact CFSG.KD.LQT.C4078h.hL
    · rw [h1, h2]; exact CFSG.KD.LQT.C4078h.hN
    · rw [h1, h3, h4]; exact CFSG.KD.LQT.C4078h.hO
  · refine coreC_sound _ hGLd duad 443520 CFSG.KD.LQT.C4078d.C CFSG.KD.LQT.C4078d.W ?_
      CFSG.KD.LQT.C4078d.hC injd ?_ ?_ ?_ ?_ ?_ ?_
    · rw [d1]; exact CFSG.KD.LQT.C4078d.hE
    · rw [d2]; exact CFSG.KD.LQT.C4078d.hg
    · rw [d2, d5]; exact CFSG.KD.LQT.C4078d.hw
    · rw [d2]; exact dcl
    · rw [d4]; exact CFSG.KD.LQT.C4078d.hL
    · rw [d1, d2]; exact CFSG.KD.LQT.C4078d.hN
    · rw [d1, d3, d4]; exact CFSG.KD.LQT.C4078d.hO
  · refine hypAC_sound _ hGLh hexad CFSG.KD.LQT.C4078h.C CFSG.KD.LQT.C4078h.W ?_
      CFSG.KD.LQT.C4078h.hC ?_ ?_ ?_ ?_ (by rw [h4]) ?_
    · rw [h1]; exact CFSG.KD.LQT.C4078h.hE
    · rw [h2]; exact CFSG.KD.LQT.C4078h.hg
    · rw [h2, h5]; exact CFSG.KD.LQT.C4078h.hw
    · rw [h2]; exact hcl
    · rw [h1, h2]; exact CFSG.KD.LQT.C4078h.hN
    · rw [h1]; exact hA
  · refine hypAC_sound _ hGLd duad CFSG.KD.LQT.C4078d.C CFSG.KD.LQT.C4078d.W ?_
      CFSG.KD.LQT.C4078d.hC ?_ ?_ ?_ ?_ (by rw [d4]) ?_
    · rw [d1]; exact CFSG.KD.LQT.C4078d.hE
    · rw [d2]; exact CFSG.KD.LQT.C4078d.hg
    · rw [d2, d5]; exact CFSG.KD.LQT.C4078d.hw
    · rw [d2]; exact dcl
    · rw [d1, d2]; exact CFSG.KD.LQT.C4078d.hN
    · rw [d1]; exact dA

end Certificates
