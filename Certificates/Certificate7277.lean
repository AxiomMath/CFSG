module

public import Certificates.Data.ASVolIK43
import Certificates.Kernel.ASVolI.K43Checks7277
import Certificates.Kernel.HMathieu.T24Glue
import Certificates.Certificate7074
import CFSG.Certificates.Kernel.ASVolI.K43Sound7277
import CFSG.Quasithin.Background.HMathieuSyl24
import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Data.Kernel.ASVolI.K43K7277
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
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
import CFSG.Quasithin.Background.A3Structure37Base
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.Quasithin.Background.A3Structure37Frattini
import CFSG.Quasithin.Background.A3Structure37KeyBase
import CFSG.Quasithin.Background.A3Structure37Schur
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.Vol2.Ch1Local
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CertificateChecks.KernelASVolI

#kc_forall_tree k43f4_all (fun i => CFSG.KS.ASVolI.f4Slice i = true) 32
  CertificateChecks.KernelASVolI.k43f4_

end CertificateChecks.KernelASVolI

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelHMathieu

theorem certificate7277 :
    CFSG.ASVolI.K43Data.listsOK () = true ∧
    CFSG.ASVolI.K43Data.f3OK () = true ∧
    CFSG.ASVolI.K43Data.f4OK () = true :=
  ⟨CFSG.KS.ASVolI.listsOK_of_K T24.packed T24.idOK KernelASVolI.k43_listsS
      KernelASVolI.k43_listsK,
    CFSG.KS.ASVolI.f3OK_of_K T24.packed KernelASVolI.k43_f3S KernelASVolI.k43_f3K,
    CFSG.KS.ASVolI.f4OK_of_K KernelASVolI.k43_f4S KernelASVolI.k43f4_all⟩

end Certificates
