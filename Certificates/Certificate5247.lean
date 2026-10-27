module

public import Certificates.Data.GH74.Ivk8L34
import Certificates.Kernel.Ivk8Norm.Final

public section

namespace Certificates

theorem certificate5247 : CFSG.Certificates.ValidSchreier Certificates.Ivk8Weak.L34.rChain ∧
    Certificates.Ivk8Weak.L34.rChain.orderCertificate = 241920 ∧
    ∀ P W : Subgroup (Equiv.Perm (Fin 42)), P ≤ CFSG.ComponentClassification.PSL3Four.S →
      W ≤ CFSG.ComponentClassification.PSL3Four.R → Nat.card P = 2 ^ 6 → IsPGroup 3 W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 42))) → W = ⊥ := CFSG.KS.Ivk8Norm.Final.l34_facts

end Certificates
