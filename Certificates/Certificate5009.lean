module

import Certificates.Kernel.Census.Q8Aut
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateHom
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CFSG in
open Subgroup in
theorem certificate5009 : (Nat.card (MulAut (QuaternionGroup 2)) = 24)
    ∧ (∀ σ : MulAut (QuaternionGroup 2),
    (∀ q, σ q * q = 1 ∨ σ q * q = QuaternionGroup.a 2) →
      ∃ q0, ∀ x, σ x = q0 * x * q0⁻¹) :=
  ⟨Census.Q8Aut.card_mulAut, Census.Q8Aut.inner_of_mul_self⟩

end Certificates
