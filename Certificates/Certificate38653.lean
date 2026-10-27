module

public import Certificates.Data.SmithL6Facts
import Certificates.Kernel.SmithL6K.GlueF

public section

namespace Certificates

open CFSG.SmithL6 in
open CFSG.SmithE (applyCols) in
theorem certificate38653 :
    (∀ i < 1395, ∀ j < 1395,
      (∃ c < 2 ^ 20, applyCols (tvCols 0) c ^^^ c = wt i) →
      (∃ c < 2 ^ 20, applyCols (tvCols 0) c ^^^ c = wt j) →
      ∃ w : List Nat, (∀ r ∈ w, r < 1953 ∧ mfPairKind 0 r = 0) ∧ e4fApplyWord w (wt i) = wt j) ∧
    ∀ l < 1953, mfPairKind 0 l = 2 → ∃ i < 1395,
      (∃ c < 2 ^ 20, applyCols (tvCols 0) c ^^^ c = wt i) ∧
      applyCols (tvCols l) (wt i) = wt i ∧
      ¬ ∃ c < 2 ^ 20, applyCols (tvCols l) c ^^^ c = wt i :=
  ⟨CertificateChecks.KernelSmithL6K.word0_holds, CertificateChecks.KernelSmithL6K.plane0_holds⟩

end Certificates
