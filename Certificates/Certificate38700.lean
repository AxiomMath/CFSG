module

public import Certificates.Kernel.SmithD6Lines.Facts
public import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned in
open CFSG.SmithD6 in
theorem certificate38700 : (lineKeys.size = 365211 ∧
      ∀ k < 365211, 0 < (linePair k).1 ∧ (linePair k).1 < (linePair k).2 ∧
        (linePair k).2 < ((linePair k).1 ^^^ (linePair k).2) ∧
        ((linePair k).1 ^^^ (linePair k).2) < 4096 ∧ qf (linePair k).1 = false ∧
        qf (linePair k).2 = false ∧ bf (linePair k).1 (linePair k).2 = false ∧
        lineIdx (linePair k).1 (linePair k).2 = k) ∧
    ∀ a ∈ singArr, ∀ b ∈ singArr, a ≠ b → bf a b = false → lineIdx3 a b (a ^^^ b) < 365211 :=
  SmithD6Lines.lines_of_pinned pinnedModel.lineKeys_toList pinnedModel.lineIdx_of_memB
    pinnedModel.lineKeys_lineIdx

end Certificates
