module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic
import Certificates.Kernel.Q16L34.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate320301 : ∃ Q : Subgroup (Equiv.Perm (Fin 42)), Q ≤ CFSG.ComponentClassification.PSL3Four.R ∧
    Nat.card ↥Q = 2 ^ 8 ∧ CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.NoQ16Q16 ↥Q :=
  ⟨KernelQ16L34.l34S, KernelQ16L34.q16L34_le_R, KernelQ16L34.q16L34_card_noQ16Q16⟩

end Certificates
