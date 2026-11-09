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
  refine ⟨g0OK_of_g0WR g0wf g0len G0W g0, conjOK_of_ent conjWfA6 conjEntA6,
    inv_of_slices invKA6 invWfA6 invEntA6 invKeysA6 fun s hs => ?_,
    gen_of_slices genKA6 genWfA6 conjWfA6 genEntA6 genKeysA6 fun s hs => ?_⟩
  · interval_cases s
    exacts [invS0, invS1, invS2, invS3, invS4, invS5, invS6, invS7]
  · interval_cases s
    exacts [⟨0, genS0⟩, ⟨98, genS1⟩, ⟨198, genS2⟩, ⟨296, genS3⟩, ⟨396, genS4⟩, ⟨496, genS5⟩,
      ⟨570, genS6⟩, ⟨670, genS7⟩]

end Certificates
