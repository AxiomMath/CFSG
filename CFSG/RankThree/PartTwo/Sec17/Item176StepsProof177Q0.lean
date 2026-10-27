module

public import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof177
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofClaims
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Late

theorem step177MeetQ_of (hQ0 : Claim17Q0) : Step177MeetQ := by
  intro G _ _ A c L Y₀ h V hV _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hMV, hVab⟩ := hV.prop
  have hYM : Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) := Subgroup.le_normalizer
  have hYW : Y₀ ≤ Subgroup.normalizer ((V ⊓ Y₀ : Subgroup G) : Set G) :=
    le_normalizer_inf (hYM.trans hMV) hYM
  have hW2 : IsPGroup 2 (V ⊓ Y₀ : Subgroup G) :=
    (Sec5.isPGroup_of_isElemAbelian hVab).to_le inf_le_left
  have hWO : V ⊓ Y₀ ≤ CFSG.Open.pCoreOf 2 Y₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hYW hW2
  have hAW : A ≤ Subgroup.normalizer ((V ⊓ Y₀ : Subgroup G) : Set G) :=
    le_normalizer_inf (h.le_normalizer_y0.trans hMV) h.le_normalizer_y0
  exact mem_scriptQ_of_le (hQ0 G A c L Y₀ h) hWO hAW


theorem step177Meet_of_claim17Q0 (hQ0 : Claim17Q0) : Step177Meet :=
  step177Meet_of (step177MeetQ_of hQ0)

end CFSG.RankThree.PartTwo.Sec17
