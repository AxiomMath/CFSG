module

import Certificates.Kernel.E27Orth.O8mGlue
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace Certificates

open Subgroup Matrix CFSG.Assembly.LowTwoRank in
theorem certificate131004 :
    ∃ S : Subgroup ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1)), Nat.card S = 81 ∧
      (∀ c ∈ S, c ≠ 1 → (∀ s ∈ S, s * c = c * s) →
        Nat.card {v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → ZMod 2 //
          ((c : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
              (ZMod 2)) *ᵥ v = v} = 4) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∉ zpowers a →
        ∃ i j : ℕ, a ^ i * b ^ j ≠ 1 ∧ Nat.card {v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → ZMod 2 //
          (((a ^ i * b ^ j : ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1))) :
            GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
              (ZMod 2)) *ᵥ v = v} ≠ 4) :=
  CertificateChecks.KernelE27Orth.O8m.o8m131004_fact

end Certificates
