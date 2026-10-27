module

public import Certificates.Data.HatA6Embed
import Certificates.Kernel.HatA6.Checks
import CFSG.Certificates.Kernel.HatA6Sound

public section

namespace Certificates

open CertificateChecks.KernelHatA6 CFSG.KC.HatA6

open CFSG.Quasithin.H13.HatE in
theorem certificate7121 :
    g0OK = true ∧
    conjOK = true ∧
    allCodes (fun m => !invHyp m || invOK m) = true ∧
    allCodes (fun m => !genHyp m || genOK m) = true := by
  refine ⟨g0OK_of_g0R g0wf g0len g0, conj, inv_of_slices fun s hs => ?_,
    gen_of_slices fun s hs => ?_⟩
  · interval_cases s
    exacts [invS0, invS1, invS2, invS3, invS4, invS5, invS6, invS7]
  · interval_cases s
    exacts [genS0, genS1, genS2, genS3, genS4, genS5, genS6, genS7]

end Certificates
