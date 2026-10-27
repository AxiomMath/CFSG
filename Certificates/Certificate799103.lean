module

public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaG24Data
import Certificates.Kernel.G24Th799103.GlueInv
import Certificates.Kernel.G24Th799103.GlueSyl

public section

namespace Certificates

open CertificateChecks.KernelG24Th CFSG.Monster.B.Co2 CFSG.EvenSporadicStandard.G24Aut in
open CFSG.RankThree.PartTwo.Sec21.Holder214Theta CFSG.Monster.B.Co2
  CFSG.EvenSporadicStandard.G24Aut in
open scoped commutatorElement in
theorem certificate799103 :
    (permOfArr 1365 g24ThC1 ^ 3 = 1 ∧ permOfArr 1365 g24ThC2 ^ 3 = 1 ∧
      permOfArr 1365 g24ThC1 * permOfArr 1365 g24ThC2 =
        permOfArr 1365 g24ThC2 * permOfArr 1365 g24ThC1 ∧
      permOfArr 1365 g24ThC1 ≠ 1 ∧ permOfArr 1365 g24ThC2 ≠ 1 ∧
      permOfArr 1365 g24ThC2 ≠ permOfArr 1365 g24ThC1 ∧
      permOfArr 1365 g24ThC2 ≠ permOfArr 1365 g24ThC1 ^ 2 ∧
      permOfArr 1365 g24ThTau ^ 2 = 1 ∧
      permOfArr 1365 g24ThTau * permOfArr 1365 xa * (permOfArr 1365 g24ThTau)⁻¹ ∈
        Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ∧
      permOfArr 1365 g24ThTau * permOfArr 1365 ya * (permOfArr 1365 g24ThTau)⁻¹ ∈
        Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ∧
      permOfArr 1365 g24ThTau ∉ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ∧
      permOfArr 1365 g24ThC1 ∈
        ⁅Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ⊓
            Subgroup.centralizer {permOfArr 1365 g24ThTau},
          Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ⊓
            Subgroup.centralizer {permOfArr 1365 g24ThTau}⁆ ∧
      permOfArr 1365 g24ThC2 ∈
        ⁅Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ⊓
            Subgroup.centralizer {permOfArr 1365 g24ThTau},
          Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ⊓
            Subgroup.centralizer {permOfArr 1365 g24ThTau}⁆) ∧
    (∀ u ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya, permOfArr 1365 g24ThTau},
      u ^ 2 = 1 → u * permOfArr 1365 g24ThC1 = permOfArr 1365 g24ThC1 * u →
      u * permOfArr 1365 g24ThC2 = permOfArr 1365 g24ThC2 * u →
      u = 1 ∨ u = permOfArr 1365 g24ThTau) ∧
    (∀ Q : Subgroup (Equiv.Perm (Fin 1365)), IsPGroup 2 Q →
      Q ≤ ⁅Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ⊓
            Subgroup.centralizer {permOfArr 1365 g24ThTau},
          Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ⊓
            Subgroup.centralizer {permOfArr 1365 g24ThTau}⁆ →
      ⁅Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ⊓
            Subgroup.centralizer {permOfArr 1365 g24ThTau},
          Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ⊓
            Subgroup.centralizer {permOfArr 1365 g24ThTau}⁆ ≤
        Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 1365))) → Q = ⊥) ∧
    (∀ E : Subgroup (Equiv.Perm (Fin 1365)),
      E ≤ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} → Nat.card E = 9 →
      ∃ g ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
        (Subgroup.closure {permOfArr 1365 g24ThC1, permOfArr 1365 g24ThC2}).map
          (MulAut.conj g).toMonoidHom = E) := by
  have ex : permOfArr 1365 xa = CFSG.Sporadic.Co1Block.xBar := CFSG.Sporadic.Co1Block.strong0_eq
  have ey : permOfArr 1365 ya = CFSG.Sporadic.Co1Block.yBar := CFSG.Sporadic.Co1Block.strong1_eq
  rw [ex, ey]
  exact ⟨basic_facts, fun _ hu => invol_eq hu, o2_tau, fun _ hE h9 => conj_E0 hE h9⟩

end Certificates
