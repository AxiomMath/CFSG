module

public import CFSG.RankThree.Native.ONTriplePresInputs
import Certificates.Kernel.Misc.Coset.ONCover

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple CFSG.CosetTable in
theorem certificate8141 : ∀ e₂ e₃ : ℕ, e₂ < 3 → e₃ < 3 → ¬ (e₂ = 1 ∧ e₃ = 1) →
    Finite (PG 8 (coverRels 1 e₂ e₃)) ∧ Nat.card (PG 8 (coverRels 1 e₂ e₃)) ≤ 460815505920 :=
  fun _ _ h₂ h₃ hne =>
    KernelMiscCoset.ONCover.card_FHat_le (by norm_num) h₂ h₃ (by omega)

end Certificates
