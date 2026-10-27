module

public import Certificates.Data.SmithD6Facts
import Certificates.Kernel.SmithD6E4f7.Glue
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

open CFSG.SmithD6 in
theorem certificate38772 : (∃ r₀ < 75735, ∀ i < 75735, (∃ c < 2 ^ 32, applyCols (tvCols 0) c ^^^ c = wt i) →
      ∃ w : List Nat, (∀ r ∈ w, r < 365211 ∧ ∀ c < 2 ^ 32,
        applyCols (tvCols r) (applyCols (tvCols 0) c) =
          applyCols (tvCols 0) (applyCols (tvCols r) c)) ∧
        w.foldr (fun r c => applyCols (tvCols r) c) (wt r₀) = wt i) ∧
    e4f7ChkPlane () = true :=
  ⟨SmithD6E4f7.e4f7Word_of_pinned pinnedModel.lineKeys_toList pinnedModel.wtArr_toList,
    SmithD6Reps.e4f7ChkPlane_of_pinned pinnedModel.lineKeys_toList pinnedModel.wt_get⟩

end Certificates
