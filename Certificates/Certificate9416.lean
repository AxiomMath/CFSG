module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubData
import CFSG.Certificates.Kernel.OpsLayKSound
import CFSG.Certificates.Kernel.OpsF2KCubQSound
import Certificates.Kernel.LocalComp.F3.McL
import Certificates.Kernel.LocalComp.F3.ON
import Certificates.Kernel.LocalComp.SporCubHQ
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.AGLEmbedding.SporCubic CFSG.KD.LC.F3 CertificateChecks.KernelLC

open CFSG.SectionRank.Native CFSG.AGLEmbedding.SporCubic in
theorem certificate9416 : ((ops3 21).cubicCheck mclSylow5HData = true)
    ∧ ((ops2 22).cubicCheck co2Sylow5HData = true)
    ∧ ((ops2 22).cubicCheck co3Sylow5HData = true)
    ∧ ((ops2 248).cubicCheck thSylow5HData = true)
    ∧ ((ops3 154).cubicCheck onSylow7HData = true) :=
  ⟨CFSG.KC.OpsLayK.cubK_sound McL.lay_ok rfl rfl McL.decA McL.decB
      ((rfl : mclSylow5HData.seedA = CFSG.Blueprint.NativeSporadic.McLSeed1).trans McL.LA_eq)
      ((rfl : mclSylow5HData.seedB = CFSG.Blueprint.NativeSporadic.McLSeed2).trans McL.LB_eq)
      McL.sylow5H_K,
    CFSG.KC.OpsF2K.cubicCheck_of_Q Co2Ops.SA.bind Co2Ops.SB.bind
      ((rfl : co2Sylow5HData.seedA = CFSG.Sporadic.Co2.Native.seedA).trans Co2Ops.SA.eq)
      ((rfl : co2Sylow5HData.seedB = CFSG.Sporadic.Co2.Native.seedB).trans Co2Ops.SB.eq)
      SporCubH.co2_Q,
    CFSG.KC.OpsF2K.cubicCheck_of_Q Co3Ops.SA.bind Co3Ops.SB.bind
      ((rfl : co3Sylow5HData.seedA = CFSG.Sporadic.Co3.Native.seedA).trans Co3Ops.SA.eq)
      ((rfl : co3Sylow5HData.seedB = CFSG.Sporadic.Co3.Native.seedB).trans Co3Ops.SB.eq)
      SporCubH.co3_Q,
    CFSG.KC.OpsF2K.cubicCheck_of_Q CertificateChecks.Th8.SA.bind CertificateChecks.Th8.SB.bind
      ((rfl : thSylow5HData.seedA = thSeedA).trans CertificateChecks.Th8.SA.eq)
      ((rfl : thSylow5HData.seedB = thSeedB).trans CertificateChecks.Th8.SB.eq)
      SporCubH.th_Q,
    CFSG.KC.OpsLayK.cubK_sound ON.lay_ok rfl rfl ON.decA ON.decB
      ((rfl : onSylow7HData.seedA = CFSG.Blueprint.NativeSporadic.ONSeed1).trans ON.LA_eq)
      ((rfl : onSylow7HData.seedB = CFSG.Blueprint.NativeSporadic.ONSeed2).trans ON.LB_eq)
      ON.sylow7H_K⟩

end Certificates
