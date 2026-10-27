
module


public import CFSG.LocalAnalysis.StandardType.L34SylowTabs
import CFSG.LocalAnalysis.StandardType.L34SylowOvergroupBase
import Certificates.Kernel.L34Syl.Data

@[expose] public section

open CFSG.StandardType.L34Sylow CFSG.PSL3Four.Native

namespace CertificateChecks.Batch465003

open CFSG.KC.L34Syl CFSG.StandardType.L34Sylow CFSG.PSL3Four.Native CertificateChecks.KernelL34Syl
open CFSG.ComponentClassification.PSL3Four (TabRep)

theorem hcardS : Nat.card ↥(closureTabs gensS) = 20160 := by
  rw [closureTabs_gensS]
  exact CFSG.ComponentClassification.PSL3Four.card_S

theorem chunk_append {P : ℕ → Prop} {A B : List ℕ} {lo k hi : ℕ}
    (hA : A.Pairwise (· < ·) ∧ ∀ x ∈ A, lo < x ∧ x ≤ k ∧ P x)
    (hB : B.Pairwise (· < ·) ∧ ∀ x ∈ B, k < x ∧ x ≤ hi ∧ P x) (hk : k ≤ hi) (hlk : lo ≤ k) :
    (A ++ B).Pairwise (· < ·) ∧ ∀ x ∈ A ++ B, lo < x ∧ x ≤ hi ∧ P x := by
  refine ⟨List.pairwise_append.mpr ⟨hA.1, hB.1, fun a ha b hb => ?_⟩, fun x hx => ?_⟩
  · have := (hA.2 a ha).2.1
    have := (hB.2 b hb).1
    omega
  · rcases List.mem_append.mp hx with h | h
    · obtain ⟨h1, h2, h3⟩ := hA.2 x h
      exact ⟨h1, by omega, h3⟩
    · obtain ⟨h1, h2, h3⟩ := hB.2 x h
      exact ⟨by have := (hB.2 x h).1; omega, h2, h3⟩

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

end CertificateChecks.Batch465003

