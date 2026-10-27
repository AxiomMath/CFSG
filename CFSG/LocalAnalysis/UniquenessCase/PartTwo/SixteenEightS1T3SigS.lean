module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Quasithin.Background.B69SL2
import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviOfComponent
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Kernel
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16t3_isSimpleGroup_of_shape {X : Type} [Group X] {n : ℕ}
    (hX : (IsSLn X n 1 ∧ 4 ≤ n) ∨ (IsSpn X n 1 ∧ 6 ≤ n) ∨ (IsOmegaPlus X n 1 ∧ 6 ≤ n) ∨
      (IsOmegaMinus X n 1 ∧ 6 ≤ n) ∨ (UC22.IsAlt X n ∧ 8 ≤ n)) :
    IsSimpleGroup X := by
  rcases hX with ⟨hSL, hn4⟩ | ⟨hSp, hn6⟩ | ⟨hOP, hn6⟩ | ⟨hOM, hn6⟩ | ⟨hAlt, hn8⟩
  ·
    obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSL
    letI : Field K := hKf
    haveI : IsSimpleGroup ↥(StatedSL n K) :=
      B69.isSimpleGroup_statedSL_two (by simpa using hKcard) (by omega)
    exact e.isSimpleGroup
  ·
    obtain ⟨hEven, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSp
    obtain ⟨k, hk⟩ := hEven
    letI : Field K := hKf
    letI : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by simpa using hKcard
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := by
      haveI : Fintype K := Fintype.ofFinite K
      exact charP_of_card_eq_prime (p := 2)
        (by rw [← Nat.card_eq_fintype_card]; exact hK2)
    have hm : 3 ≤ n / 2 := by omega
    haveI : IsSimpleGroup (StatedSp (n / 2) K) :=
      CFSG.StandardType.SpJoin.isSimpleGroup_statedSp_of_three_le hm
    exact e.isSimpleGroup
  ·
    obtain ⟨hEven, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hOP
    obtain ⟨k, hk⟩ := hEven
    letI : Field K := hKf
    have hm : 3 ≤ n / 2 := by omega
    haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus
        (K := K) (n := n / 2) hm
    exact e.isSimpleGroup
  ·
    rcases eq_or_lt_of_le (show 6 ≤ n from hn6) with h6 | h8
    · exact s16c1_isSimpleGroup_of_isOmegaMinus_six (h6.symm ▸ hOM)
    · obtain ⟨hEven, K, hKf, hKfin, b, c, hKcard, hirr, ⟨e⟩⟩ := hOM
      obtain ⟨k, hk⟩ := hEven
      letI : Field K := hKf
      letI : Finite K := hKfin
      have hm : 4 ≤ n / 2 := by omega
      haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) :=
        CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
          (K := K) (n := n / 2) (b := b) (c := c) hm hirr
      exact e.isSimpleGroup
  ·
    obtain ⟨e⟩ := hAlt
    haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    exact e.isSimpleGroup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
