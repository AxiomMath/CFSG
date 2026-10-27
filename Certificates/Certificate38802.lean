module

public import Certificates.Data.SmithD6E23a
import Certificates.Kernel.SmithD6Ea.Facts
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned in
open CFSG.SmithD6 in
theorem certificate38802 : ∀ p ∈ ea7I, ∃ i < 75735, applyCols (tvCols 0) (wt i) = wt i ∧
    applyCols (tvCols 31899) (wt i) = wt i ∧
    ∃ c < 2 ^ 32, applyCols (tvCols p) c ^^^ c = wt i :=
  SmithD6Ea.ea7F3_of_pinned pinnedModel.lineKeys_toList pinnedModel.lineIdx_of_memB
    pinnedModel.lineKeys_lineIdx pinnedModel.wt_get

end Certificates
