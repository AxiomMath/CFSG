module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec20.Alt20

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem step2053_core {G : Type} [Group G] {M N : Subgroup G} {c : G} (hK : KType20 M N c)
    (hL2 : ∀ n : ℕ, Even n → 0 < n →
      Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
        CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) →
      ¬ 4 ∣ (M ⊓ N).relIndex M → False) : KIsL3 M c := by
  rcases hK with ⟨n, hn, hiso, -⟩ | ⟨n, hn, hn0, hiso, hidx⟩
  · exact ⟨n, hn, hiso⟩
  · exact (hL2 n hn hn0 hiso hidx).elim

theorem step2053_of (h189 : Sec18.Item189) (hL2 : Step2053L2) : Step2053 := by
  intro G _ _ A M L N c T hT h2
  obtain ⟨H, hH18, hH187, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  obtain ⟨-, -, hcase⟩ := h189 G A M H c hH18 hH187
  rw [← hL, ← hN] at hcase
  exact step2053_core hcase (hL2 G A M L N c T hT h2)

end CFSG.RankThree.PartTwo.Sec20
