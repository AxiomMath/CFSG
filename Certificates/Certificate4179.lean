module

public import Certificates.Kernel.J4Loc.C15Asm

public section

namespace Certificates

open CertificateChecks.KernelJ4Loc

open CFSG.Quasithin.J4Loc in
theorem certificate4179 :
    TrioZ.ncard = 15 ∧
    (∀ W ∈ TrioZ, wordImgF wordZA (wordImgF wordZB W) = wordImgF wordZB (wordImgF wordZA W) ∧
      wordImgF wordZA (wordImgF wordZA (wordImgF wordZA W)) = W ∧
      wordImgF wordZB (wordImgF wordZB (wordImgF wordZB W)) = W) ∧
    ∃ W ∈ TrioZ, wordImgF wordZA W ≠ W ∧ wordImgF wordZB W ≠ W ∧
      wordImgF wordZB W ≠ wordImgF wordZA W ∧
      wordImgF wordZB W ≠ wordImgF wordZA (wordImgF wordZA W) :=
  ⟨k4179_ncard, fun _ hW => k4179_rel hW, k4179_ne⟩

end Certificates
