module

public import Certificates.Data.TriD4Phi
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Perm
import Certificates.Kernel.D4.FieldFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.Open Subgroup in
theorem certificate707011 :     ∀ B : Subgroup (Equiv.Perm (Fin 2457)), B ≤ zpowers d4Phi ⊔ d4P → IsElemAbelian 3 B →
      Nat.card B = 27 → ¬ B ≤ d4P → ∀ u ∈ B, u ∈ d4P → u ≠ 1 →
      IsSolvable ↥(centralizer {u} ⊓ d4P) ∨
        ∃ n ∈ d4P, n ∈ normalizer (B : Set (Equiv.Perm (Fin 2457))) ∧ n * u * n⁻¹ ∉ zpowers u :=
  KernelD4.field_facts

end Certificates
