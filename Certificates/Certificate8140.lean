module

public import CFSG.RankThree.Native.ONTriplePresInputs
import Certificates.Kernel.Misc.Coset.ONCover

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple CFSG.CosetTable in
theorem certificate8140 : ∀ e₂ e₃ : ℕ, e₂ < 3 → e₃ < 3 → ¬ (e₂ = 0 ∧ e₃ = 0) →
    Finite (PG 8 (coverRels 0 e₂ e₃)) ∧ Nat.card (PG 8 (coverRels 0 e₂ e₃)) ≤ 460815505920 :=
  fun _ _ h₂ h₃ hne =>
    KernelMiscCoset.ONCover.card_FHat_le (by norm_num) h₂ h₃ (by omega)

end Certificates
