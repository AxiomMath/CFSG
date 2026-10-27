module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusSuzInputs
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFusSound
import Certificates.Kernel.FusLay.Suz

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9472 : fusCheck (ops3 64) NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2
    betaSuzP3N betaSuzP3Prog betaSuzP3 = true :=
  CFSG.KC.OpsLayK.fusL_sound Suz.lay_ok rfl rfl Suz.decA Suz.decB Suz.LA_eq Suz.LB_eq
    Suz.fus9472_K

end Certificates
