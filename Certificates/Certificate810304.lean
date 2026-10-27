module

public import CFSG.Sporadic.LyI301.Inputs
import CFSG.Certificates.Kernel.LyI301.Sound
import Certificates.Kernel.LyI301.Glue

public section

open CFSG.Sporadic.LyI301 CFSG.Certificates.Kernel.LyI301

namespace Certificates

open CFSG.Sporadic.LyI301 in
theorem certificate810304 :
    (∀ σ₃ σ₈, lySplit σ₃ σ₈ * lyX1 = lyX1 * lySplit σ₃ σ₈ →
      (∀ i, lySplit σ₃ σ₈ * lyU i * (lySplit σ₃ σ₈)⁻¹ ∈ lyV) → lySplit σ₃ σ₈ ^ 24 = 1) ∧
    (∀ σ₃ σ₈, (∀ i, lySplit σ₃ σ₈ * lyU i * (lySplit σ₃ σ₈)⁻¹ ∈ lyV) →
      lySplit σ₃ σ₈ ∉ lyV → lySplit σ₃ σ₈ * lySplit σ₃ σ₈ ∈ lyV →
      ∃ b ∈ lyConj, lySplit σ₃ σ₈ * (b * lySplit σ₃ σ₈ * b⁻¹) * (lySplit σ₃ σ₈)⁻¹ *
        (b * lySplit σ₃ σ₈ * b⁻¹)⁻¹ ∉ lyV) :=
  ⟨fun σ₃ σ₈ _ hN => pow_24 _ (lySplit_small σ₃ σ₈) hN,
    fun σ₃ σ₈ hN hg hsq =>
      inv_facts CFSG.KC.LyI301.ly810304rows _ (lySplit_small σ₃ σ₈) hN hg hsq⟩

end Certificates
