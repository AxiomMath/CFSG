module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuBorelInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzWords
import Certificates.Kernel.RuBorel.Final

public section

set_option maxRecDepth 100000

namespace Certificates

open CertificateChecks.KernelRuBorel

open CFSG.EvenSporadicStandard.Induction.RuSz CFSG.Sporadic.RuSchreier in
theorem certificate27121 :
    kG x0Word * kG x0Word = 1 ∧ kG x0Word ≠ 1 ∧
    (∀ w ∈ borelGens, ∀ r ∈ Subgroup.closure ({sG, tG} : Set (Equiv.Perm (Fin 4060))),
      r * kG x0Word = kG x0Word * r →
        r * ((kG w)⁻¹ * kG x0Word * kG w) = ((kG w)⁻¹ * kG x0Word * kG w) * r) ∧
    (∀ w ∈ hBWords, kG w ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩) ∧
    (∀ p : Fin 4060, (∀ w ∈ hBWords, kG w p = p) → p.val ∈ [0, 1, 3645, 3692]) ∧
    kG k1Word ⟨0, by norm_num⟩ = ⟨1, by norm_num⟩ ∧
    (∀ g ∈ ruP, g ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ → g ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ →
      g * kG n1Word = kG n1Word * g → g * kG n2Word = kG n2Word * g → g = 1) :=
  ⟨x_sq, x_ne_one, fun _ hw _ hr hrx => comm_y hw hr hrx, fun _ hw => h_zero hw, fix_mem,
    k1_zero, fun _ hg h0 h1 c1 c2 => eq_one_tail hg h0 h1 c1 c2⟩

end Certificates
