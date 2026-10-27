module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddY9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem r920odd_of_inputs (D : Data G) (hK3 : StronglyEmbeddedThree) (hK : UCK.K332Cyc)
    (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hKF7 : KF7Use D)
    (hgt : ∀ (L D₃ Y H : Subgroup G) (q : ℕ), Slice D L D₃ Y H q → 7 < q → ∀ E : Subgroup G,
      F09.Hyp91 D Y H E → (∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
        normalizer (A : Set G) ≤ D.M) → False)
    (heq : ∀ (L D₃ Y H : Subgroup G) (q : ℕ), Slice D L D₃ Y H q → q = 7 → ∀ E : Subgroup G,
      F09.Hyp91 D Y H E → (∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
        normalizer (A : Set G) ≤ D.M) → False) :
    R920odd D := by
  intro L D₃ Y H hyp hYL q hq hq5 hshape
  by_contra hno
  push Not at hno
  have S : Slice D L D₃ Y H q := ⟨⟨hyp, hYL, Shape919.of_isL2Odd hq hq5 hshape⟩, hq, hq5, hshape⟩
  obtain ⟨E, hE⟩ := S.exists_hyp91 hK3 hK h82 hSg h614 h76 hKF7
  have hq6 : q ≠ 6 := by
    rintro rfl
    norm_num at hq
  rcases (by omega : q = 7 ∨ 7 < q) with h7 | h7
  · exact heq L D₃ Y H q S h7 E hE hno
  · exact hgt L D₃ Y H q S h7 E hE hno

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
