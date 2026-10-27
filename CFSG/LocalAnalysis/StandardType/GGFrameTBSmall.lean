module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBBody
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeVac
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestRank
import CFSG.LocalAnalysis.StandardType.GGFrameTBVacuous
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoordHA

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly

theorem frameTBBody_of_card_lt {lab : LargeEvenLabel} {k : ℕ} (hk : k ≤ 6)
    (h : LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ k) :
    LargeEvenLabelAll lab (frameTBBody lab) :=
  h.mono fun R _ I _ hX r hr _ =>
    ⟨fun L' _ _ ψ A hA =>
        absurd hA (not_ggTorusTBGroup_of_card_lt (by norm_num) (by omega) hX),
      fun L' _ _ ψ A hA =>
        absurd hA (not_ggTorusTBGroup_of_card_lt (by norm_num) (by omega) hX)⟩

theorem frameTBBody_twoThreeSmall {lab : LargeEvenLabel}
    (h : StdSubRestThree.GGTwoThreeSmallLabel 3 lab) :
    LargeEvenLabelAll lab (frameTBBody lab) :=
  frameTBBody_of_card_lt (k := 3) (by norm_num)
    (StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall h)

theorem frameTBBody_linearTwo {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGLinearTwoLabel lab) : LargeEvenLabelAll lab (frameTBBody lab) :=
  frameTBBody_of_card_lt (k := 3) (by norm_num)
    (largeEvenLabelAll_card_lt_linearTwo Nat.prime_three (by norm_num) hlab h)

theorem recipeUnitary_card_lt_two {d : ℕ} (hd : 4 ≤ d) (hd6 : d ≤ 6) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeUnitary d (2 ^ 1) Q) :
    LargeEvenRecipeUnitary d (2 ^ 1) fun R _ I F => Q R I F ∧ ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 6 := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun X hXI hX => ?_⟩
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    rintro h
    have h1 : d = 3 := congrArg Prod.fst h
    omega
  have hcard := HdRo7SU.hdRo7SUKCoordAux_card_le_unitary
    (TableBU.unitaryFieldData_of_card hK le_rfl) hK (by omega : 3 ≤ d) hdq
    Nat.prime_three (by norm_num : 3 ∣ 2 ^ 1 + 1) hX hXI
  exact hcard.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))

theorem frameTBBody_twA_small {m : ℕ} (hm : 3 ≤ m) (hm5 : m ≤ 5) :
    LargeEvenLabelAll ⟨.twA, m, 1⟩ (frameTBBody ⟨.twA, m, 1⟩) :=
  frameTBBody_of_card_lt le_rfl fun Q hQ =>
    recipeUnitary_card_lt_two (d := m + 1) (by omega) (by omega) hQ

theorem frameTBBody_twD_three :
    LargeEvenLabelAll ⟨.twD, 3, 1⟩ (frameTBBody ⟨.twD, 3, 1⟩) := by
  refine frameTBBody_of_card_lt le_rfl fun Q hQ => ?_
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_neg (by norm_num : ¬ (3 = 2)), if_pos rfl] at hQ ⊢
  exact recipeUnitary_card_lt_two (d := 4) (by omega) (by omega) hQ

end CFSG.StandardType.FrameRoute

end
