module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi23Inputs
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFillSound
import Certificates.Kernel.FusLay.Fi23P3

public section

open CertificateChecks.KernelTc CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9484 : fusCheck (ops3 253) NativeSporadic.Fi23Seed1 NativeSporadic.Fi23Seed2
    betaFi23P3N betaFi23P3Prog betaFi23P3 = true :=
  CFSG.KC.OpsLayK.fusRen_sound (S := fun i => Fi23P3.SL.getD i []) Fi23.lay_ok rfl rfl
    Fi23.decA Fi23.decB Fi23.LA_eq Fi23.LB_eq (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) Fi23P3.ren rfl Fi23P3.ch_all Fi23P3.fin_in
    Fi23P3.fa_all Fi23P3.seeds

end Certificates
