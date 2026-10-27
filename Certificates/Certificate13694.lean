module

public import CFSG.Certificates.Kernel.MonsterPcSeven.Cover
import Certificates.Kernel.MonsterPcSeven.Census

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.MonPcSeven (PcHyp AutRel autAt targets dec) in
open CFSG.KC.BM.PcFive (psi) in
theorem certificate13694 : ∀ {G : Type} [Group G] [Finite G] {u : G} {q : Fin 4 → G} {z : G}, PcHyp u q z →
    z ≠ 1 → ∀ {m : ℕ}, Nat.card G = 7 ^ 6 * m → ¬ 7 ∣ m → ∀ Good : G → Prop,
    (∀ s c : G, Good s → Good (c * s * c⁻¹)) →
    (∀ s : G, s ^ 7 = 1 → ∀ k : ℕ, Nat.Coprime k 7 → (Good (s ^ k) ↔ Good s)) →
    (∀ j < 2, ∃ g, AutRel u q z g (autAt j)) → (∀ i ∈ targets, Good (psi u q z (dec i))) →
    ∀ s : G, orderOf s = 7 → Good s :=
  fun H hz _ hcard hm Good hconj hpow hN hT =>
    CFSG.KC.MonPcSeven.forall_of_census H KernelM7.PcSeven.phiOK_true hz
      KernelM7.PcSeven.censusFact hcard hm Good hconj hpow hN hT

end Certificates
