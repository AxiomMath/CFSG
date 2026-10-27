module

public import Certificates.Data.CFSGNative.CTP.StrongP
import CFSG.Certificates.Kernel.OpsLayKSound
import CFSG.Certificates.Kernel.OpsF2KCubQSound
import CFSG.Certificates.Kernel.OpsCubNSound
import Certificates.Kernel.LocalComp.StrongP14954
import Certificates.Kernel.LocalComp.StrongP14954ThQ
import Certificates.Kernel.MatCert.StrongPF5
import Certificates.Kernel.MatCert.GlueLy
import Certificates.Kernel.TcGen.F5Glue
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.F3 CFSG.KC.OpsK CFSG.Blueprint
open CertificateChecks.KernelLC CertificateChecks.KernelMC CertificateChecks.KernelSporSch
open CertificateChecks.KernelTc CFSG.KS.SporSch.LyM

open CFSG.SectionRank.Native in
theorem certificate14954 : ((ops3 21).cubicCheck mclSylow5Data = true)
    ∧ ((opsP 5 111).cubicCheck lySylow5Data = true)
    ∧ ((ops3 154).cubicCheck onSylow7Data = true)
    ∧ ((ops2 22).cubicCheck co3Sylow5Data = true)
    ∧ ((ops2 22).cubicCheck co2Sylow5Data = true)
    ∧ ((opsP 5 133).cubicCheck hnSylow5Data = true)
    ∧ ((ops2 248).cubicCheck thSylow5Data = true) :=
  ⟨CFSG.KC.OpsLayK.cubK_sound McL.lay_ok rfl rfl McL.decA McL.decB
      ((rfl : mclSylow5Data.seedA = NativeSporadic.McLSeed1).trans McL.LA_eq)
      ((rfl : mclSylow5Data.seedB = NativeSporadic.McLSeed2).trans McL.LB_eq)
      StrongP14954.mcl_K,
    CFSG.KC.OpsCubN.cubicCheck_of_N HL
      (lyA : (opsP 5 111).decode lySylow5Data.seedA = HL.U LyBS.A)
      (lyB : (opsP 5 111).decode lySylow5Data.seedB = HL.U LyBS.B)
      (vldL LyBS.vA) (vldL LyBS.vB) StrongPF5.ly_K,
    CFSG.KC.OpsLayK.cubK_sound ON.lay_ok rfl rfl ON.decA ON.decB
      ((rfl : onSylow7Data.seedA = NativeSporadic.ONSeed1).trans ON.LA_eq)
      ((rfl : onSylow7Data.seedB = NativeSporadic.ONSeed2).trans ON.LB_eq)
      StrongP14954.on_K,
    CFSG.KC.LocalComp.Cub.cubicCheck_of_K Co3Ops.SA.bind Co3Ops.SB.bind
      ((rfl : co3Sylow5Data.seedA = CFSG.Sporadic.Co3.Native.seedA).trans Co3Ops.SA.eq)
      ((rfl : co3Sylow5Data.seedB = CFSG.Sporadic.Co3.Native.seedB).trans Co3Ops.SB.eq)
      StrongP14954.co3_K,
    CFSG.KC.LocalComp.Cub.cubicCheck_of_K Co2Ops.SA.bind Co2Ops.SB.bind
      ((rfl : co2Sylow5Data.seedA = CFSG.Sporadic.Co2.Native.seedA).trans Co2Ops.SA.eq)
      ((rfl : co2Sylow5Data.seedB = CFSG.Sporadic.Co2.Native.seedB).trans Co2Ops.SB.eq)
      StrongP14954.co2_K,
    CFSG.KC.OpsCubN.cubicCheck_of_N (homP HN.consts (by decide))
      (HN.rowsA : (opsP 5 133).decode hnSylow5Data.seedA = unpackL HN.lay.d HN.lay.w HN.lay.S HN.A)
      (HN.rowsB : (opsP 5 133).decode hnSylow5Data.seedB = unpackL HN.lay.d HN.lay.w HN.lay.S HN.B)
      HN.pay.2.2.1 HN.pay.2.2.2 StrongPF5.hn_K,
    CFSG.KC.OpsF2K.cubicCheck_of_Q CertificateChecks.Th8.SA.bind
      CertificateChecks.Th8.SB.bind
      ((rfl : thSylow5Data.seedA = thSeedA).trans CertificateChecks.Th8.SA.eq)
      ((rfl : thSylow5Data.seedB = thSeedB).trans CertificateChecks.Th8.SB.eq)
      StrongP14954Th.th_Q⟩

end Certificates
