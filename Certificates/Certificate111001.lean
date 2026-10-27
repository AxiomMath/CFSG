module

public import Certificates.Data.Fi22FiveD4
import Certificates.Kernel.Sporadic.Fi22.D4Glue
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModelBase

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSpor.Fi22D4

open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Five.D4 in
open CFSG.Monster.B.Co2 CFSG.EvenSmallLie.OmegaEight in
theorem certificate111001 :
    (ordList.length = 360 ∧ ordList.Nodup ∧ ∀ p ∈ ordList, p < 3510) ∧
    (∀ t ∈ [xA, yA, hA, n1A, n2A, zA], ∀ g : Equiv.Perm (Fin 3510), Rep 3510 t g →
      ∀ p : Fin 3510, (p : ℕ) ∈ ordList → ((g p : Fin 3510) : ℕ) ∈ ordList) ∧
    (∀ g : Equiv.Perm (Fin 3510), Rep 3510 (evalW [1]) g →
      ∃ p : Fin 3510, (p : ℕ) ∈ ordList ∧ ((g p : Fin 3510) : ℕ) ∉ ordList) ∧
    (∀ t ∈ [g1A, g2A], ∀ g : Equiv.Perm (Fin 3510), Rep 3510 t g →
      ∀ σ : Equiv.Perm (Fin 360),
        (∀ (k : Fin 360) (p : Fin 3510), (p : ℕ) = ordList[(k : ℕ)]! →
          ((g p : Fin 3510) : ℕ) = ordList[((σ k : Fin 360) : ℕ)]!) → σ ∈ autT) ∧
    (∀ X Y : Equiv.Perm (Fin 3510), Rep 3510 xA X → Rep 3510 yA Y →
      ∀ i j : ℕ, i < 5 → j < 5 → (i ≠ 0 ∨ j ≠ 0) →
        ∃ p : Fin 3510, (p : ℕ) ∈ ordList ∧ (X ^ i * Y ^ j) p ≠ p) :=
  ⟨set_facts, pres_facts, out_fact, res_facts, faith_fact⟩

end Certificates
