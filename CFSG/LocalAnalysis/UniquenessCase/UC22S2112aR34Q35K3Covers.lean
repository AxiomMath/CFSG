module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35PermE
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K3Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

theorem kq35PermFive_of_covers
    (hSp3 : ∀ (K : Type) [Field K], Nat.card K = 3 →
      CFSG.GroupTheory.SylowPQMaximal 2 5 (StatedSp 2 K))
    (hSp5 : ∀ (K : Type) [Field K], Nat.card K = 5 →
      CFSG.GroupTheory.SylowPQMaximal 2 5 (StatedSp 2 K))
    (hSU : ∀ (K : Type) [Field K], Nat.card K = 9 →
      CFSG.GroupTheory.SylowPQMaximal 2 5 (StatedSU 4 3 K))
    (hO7 : ∀ (K : Type) [Field K], Nat.card K = 3 →
      CFSG.GroupTheory.SylowPQMaximal 2 5 (StatedOmega (StatedQuadOdd 3 K)))
    (hG2 : ∀ (K : Type) [Field K], Nat.card K = 5 →
      CFSG.GroupTheory.SylowPQMaximal 2 5 (CFSG.Blueprint.AdjointQuotient .G2 K)) :
    KQ35PermFive := by
  apply kq35PermFive_of_sylowPQMaximal
  intro X _ _ _ t n p ht hX
  rcases ht with ⟨rfl, rfl, rfl | rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact uc22s2112r34q35_sylowPQMaximal_psp (Or.inl rfl) hX hSp3
  · exact uc22s2112r34q35_sylowPQMaximal_psp (Or.inr rfl) hX hSp5
  · exact uc22s2112r34q35_sylowPQMaximal_psu hX hSU
  · exact uc22s2112r34q35_sylowPQMaximal_omegaOdd hX hO7
  · exact uc22s2112r34q35_sylowPQMaximal_g2 hX hG2

end CFSG.LocalAnalysis.UniquenessCase.UC22
