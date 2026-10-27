module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E6
public import CFSG.LocalAnalysis.UniquenessCase.UC6K620ExcAlt
public import CFSG.LocalAnalysis.UniquenessCase.UC6K620ExcFi22

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem k620excB_holds :
    ∀ (X : Type) [Group X] [Finite X], ((∃ n : ℕ, 13 ≤ n ∧ IsAlt X n) ∨ IsSpor X .Fi22) →
      ∀ N : Subgroup X, ¬ IsStronglyPEmbedded 3 N := by
  intro X _ _ hX N
  rcases hX with ⟨n, hn, ⟨e⟩⟩ | h
  · exact not_isStronglyPEmbedded_three_of_alt (by omega) e N
  · exact not_isStronglyPEmbedded_three_of_fi22 h N

@[expose] def K620ExcA : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (Y : Subgroup X) [Y.Normal],
      Odd (Nat.card Y) → (∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q Y ≤ 3) →
      ((∃ n : ℕ, 13 ≤ n ∧ IsAlt (X ⧸ Y) n) ∨ IsSpor (X ⧸ Y) .Fi22) →
      3 < CFSG.Open.twoLocalPrimeRank 3 X

theorem k620exc_of_A (h : K620ExcA) : K620Exc :=
  And.intro h k620excB_holds

end CFSG.LocalAnalysis.UniquenessCase.UCK
