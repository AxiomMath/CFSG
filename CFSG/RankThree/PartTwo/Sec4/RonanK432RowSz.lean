module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
public import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem outerRow_of_not_three_dvd_card {S : Type} [Group S] [Finite S] (h : ¬ 3 ∣ Nat.card S) :
    OuterRow S :=
  fun h3 => absurd h3 h

theorem rowOf_suzuki (m : ℕ)
    (hm : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    RowOf (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨-, a, -, K, _, _, hf, hK', ⟨θ⟩⟩ := Census.suzukiModel_of_index m hm
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have h3 : ¬ 3 ∣ Nat.card S := by
    rw [Nat.card_congr (e.trans θ).toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.not_three_dvd_card_suzukiGroup hK
  exact ⟨listRow_of_not_three_dvd h3, outerRow_of_not_three_dvd_card h3⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
