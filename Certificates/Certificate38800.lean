module

public import Certificates.Data.SmithD6E23a
import Certificates.Kernel.SmithD6Ea.Facts
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

theorem certificate38800 : CFSG.SmithD6.ea7ChkCols = true ∧ CFSG.SmithD6.ea7ChkBits = true ∧ CFSG.SmithD6.ea7ChkW = true ∧ CFSG.SmithD6.ea7ChkF4 = true :=
  ⟨SmithD6Ea.ea7ChkCols_of_pinned pinnedModel.lineKeys_toList pinnedModel.lineIdx_of_memB
      pinnedModel.lineKeys_lineIdx,
    SmithD6Ea.ea7ChkBits_of_pinned pinnedModel.lineKeys_toList pinnedModel.lineIdx_of_memB
      pinnedModel.lineKeys_lineIdx,
    SmithD6Ea.ea7ChkW_of_pinned pinnedModel.wt_get,
    SmithD6Ea.ea7ChkF4_of_pinned pinnedModel.lineKeys_toList pinnedModel.lineIdx_of_memB
      pinnedModel.lineKeys_lineIdx⟩

end Certificates
