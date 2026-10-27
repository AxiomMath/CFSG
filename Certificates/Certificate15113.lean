
module

public import Certificates.Kernel.Sporadic.L2C.All

public section

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG.Sporadic.SuzRecog in
theorem certificate15113 : LevelTwoCover.coverBaseOK = true ∧ LevelTwoCover.coverLiftOK = true ∧
    LevelTwoCover.coverDeckOK = true ∧ LevelTwoCover.CoverElim ∧
    LevelTwoCover.coverLocOK = true :=
  ⟨L2CG.base_true, L2CG.lift_true, L2CG.deck_true, L2CG.elim_true, L2CG.loc_true⟩

end Certificates
