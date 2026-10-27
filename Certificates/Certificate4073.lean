module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKHeInputs
import Certificates.Kernel.LocalQT.Base.C4073
import Certificates.Kernel.LocalQT.Base.C4073H
import Certificates.Kernel.LocalQT.Base.C4073W
import Certificates.Kernel.LocalQT.Base.C4073Q
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
open CFSG.Open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.He in
open CFSG.Blueprint.NativeSporadic (Carrier) in
theorem certificate4073 : (FusionCert.FusionCertS 8330 heB heTa heTb heProg heQp heEnum.1 heEnum.2.1 heEnum.2.2 10 heZI
            heWit heGW) :=
  CFSG.KD.LQT.C4073.cert

end Certificates
