module

public import CFSG.Sporadic.Co2InvCheckInputs
import Certificates.Kernel.Sporadic.Co2Inv.Recs
import Certificates.Kernel.Sporadic.Co2Inv.Gens

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Co2InvS CertificateChecks.KernelSpor.Co2Inv

open CFSG.Sporadic.Co2Inv CFSG.Certificates.Native CFSG.Sporadic.Co2Cert in
theorem certificate3118 : (gensCheck (rawLevels 2300 co2StrongArrs co2BaseArr) co2PosTable = true)
    ∧ (candCheck = true)
    ∧ (rankCheck = true)
    ∧ (enumCheck enumS candYs = true) :=
  ⟨gens_check, cand_check, rank_check, enumCheck_of_K recsK ybind reps_at⟩

end Certificates
