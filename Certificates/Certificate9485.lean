module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi24Inputs
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFillSound
import Certificates.Kernel.FusLay.Fi24P3

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9485 : fusCheck (ops3 781) NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2
    betaFi24P3N betaFi24P3Prog betaFi24P3 = true :=
  CFSG.KC.OpsLayK.fusRen_sound (S := fun i => Fi24P3.SL.getD i []) Fi24.lay_ok rfl rfl
    Fi24.decA Fi24.decB Fi24.LA_eq Fi24.LB_eq (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) Fi24P3.ren rfl Fi24P3.ch_all Fi24P3.fin_in
    Fi24P3.fa_all Fi24P3.seeds

end Certificates
