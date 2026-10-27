module

public import Certificates.Data.SmithD6Facts
import Certificates.Kernel.SmithD6Reps.Glue
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

theorem certificate38771 : CFSG.SmithD6.mf7ChkReps () = true ∧ CFSG.SmithD6.mf7ChkRepCls () = true :=
  ⟨SmithD6Reps.mf7ChkReps_of_pinned pinnedModel.lineKeys_toList pinnedModel.wtIdx_lt_iff_memB,
    SmithD6Stab.mf7ChkRepCls_true pinnedModel.lineKeys_toList⟩

end Certificates
