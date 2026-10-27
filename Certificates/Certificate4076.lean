module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRuInputs
import Certificates.Kernel.LocalQT.Base.C4076
import Certificates.Kernel.LocalQT.Base.C4076B
import Certificates.Kernel.LocalQT.Base.C4076H
import Certificates.Kernel.LocalQT.Base.C4076C
import Certificates.Kernel.LocalQT.Base.C4076W
import Certificates.Kernel.LocalQT.Base.C4076Q
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 in
open CFSG.Open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.Ru.Native (ruData) in
open CFSG.Blueprint.NativeSporadic (Carrier) in
theorem certificate4076 : (FusionCert.FusionCertS ruData.n ruB ruTa ruTb ruProg ruQp ruEnum.1 ruEnum.2.1 ruEnum.2.2 14
            ruZI ruWit ruGW) :=
  CFSG.KD.LQT.C4076.cert

end Certificates
