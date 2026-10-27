module

public import Certificates.Data.DoubleCoverRanks
import CFSG.Certificates.Kernel.OpsF2KMcertQSound
import Certificates.Kernel.SectionRankHS.FactsQ
import all CFSG.Blueprint.NativeSporadic

public section

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native
open CertificateChecks.KernelSRHS

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native in
theorem certificate8093 : (e8Check (ops2 20) hsE8Data = true) ∧ (e8Check (ops2 28) ruE8Data = true) :=
  ⟨CFSG.KC.OpsF2K.e8Check_of_K SA.bind SB.bind
      ((rfl : hsE8Data.seedA = CFSG.Blueprint.NativeSporadic.HSSeed1).trans SA.eq)
      ((rfl : hsE8Data.seedB = CFSG.Blueprint.NativeSporadic.HSSeed2).trans SB.eq)
      (CFSG.KC.OpsF2K.e8K_of_Q e8HS_Q),
    CFSG.KC.OpsF2K.e8Check_of_K RA.bind RB.bind
      ((rfl : ruE8Data.seedA = CFSG.Blueprint.NativeSporadic.RuSeed1).trans RA.eq)
      ((rfl : ruE8Data.seedB = CFSG.Blueprint.NativeSporadic.RuSeed2).trans RB.eq)
      (CFSG.KC.OpsF2K.e8K_of_Q e8Ru_Q)⟩

end Certificates
