module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusONInputs
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFillSound
import Certificates.Kernel.FusLay.ON

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9475 : fusCheck (ops3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2
    betaONP3N betaONP3Prog betaONP3 = true :=
  CFSG.KC.OpsLayK.fusRen_sound (S := fun i => ON.SL.getD i []) ON.lay_ok rfl rfl
    ON.decA ON.decB ON.LA_eq ON.LB_eq (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ON.ren rfl ON.ch_all ON.fin_in
    ON.fa_all ON.seeds

end Certificates
