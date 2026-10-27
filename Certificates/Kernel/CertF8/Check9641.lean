module

public import Certificates.Data.Kernel.CertF8.D48

public section

namespace Certificates.Kernel.CertF8

open CFSG.KC.CertF8.D48 CFSG.AGLEmbedding.ChevOuterD48

theorem ch9641E : d48EQ = true := by
  decide +kernel

theorem ch9641Hyp : d48HypQ = true := by
  decide +kernel

theorem ch9641N : d48NQ = true := by
  decide +kernel

theorem ch9641Slp : d48SlpQ = true := by
  decide +kernel

theorem ch9641NHyp : ∀ j ∈ List.range numN, nHyp j < 5 := by
  decide +kernel

theorem ch9641SlpIdx :
    (∀ x ∈ d48Slp1, x.1 < 24 ∧ ∀ i ∈ x.2, i < 2 * numN) ∧
    (∀ x ∈ d48Slp2, x.1 < 24 ∧
      ∀ i ∈ x.2, i < 2 * numN ∨ (2 * numN ≤ i ∧ (i - 2 * numN) ∈ d48Slp1.map (·.1))) ∧
    (∀ k ∈ List.range 24, k ∈ (d48Slp1 ++ d48Slp2).map (·.1)) := by
  decide +kernel

end Certificates.Kernel.CertF8

end
