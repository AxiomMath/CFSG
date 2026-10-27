module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4ModelCoords
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup

theorem exists_isSumZeroCoords_of_isLie811_l4
    {Y : Type} [Group Y] [Finite Y] {r f : ℕ}
    (hY : IsLie811 Y .l4 r f) {A : Subgroup Y} (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c, IsSumZeroCoords A c := by
  have hZ : center Y = ⊥ :=
    center_eq_bot_of_isLie811_of_ne hY (by decide) fun h => absurd h (by decide)
  have hZ3 : ¬ 3 ∣ Nat.card (center Y) := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  obtain ⟨-, -, -, -, ⟨hmod, hM⟩ | ⟨hmod, hM⟩⟩ := hY
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hM.statedClassicalModel_of_ne_zero (by norm_num)
    exact K6L4.exists_isSumZeroCoords_of_equiv_statedSL (by omega) (center Y) hZ3 e hA h27
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hM.statedClassicalModel_of_ne_zero (by norm_num)
    exact K6L4.exists_isSumZeroCoords_of_equiv_statedSU (q := r ^ f) hcard
      (by omega) (center Y) hZ3 e hA h27

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
