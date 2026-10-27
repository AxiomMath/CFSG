module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporCore
import CFSG.Sporadic.Bridge.J1
import CFSG.Sporadic.Bridge.J3Surj
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.J1
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.J3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG.RankThree.PartTwo.Sec4 (Spor)

theorem k150s_m11 {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .M11) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M11 ≃* Spor .M11 := b
  refine k150s_row_of_not_dvd (hJ.not_dvd ?_ ?_) <;>
  · rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M11]
    norm_num

theorem k150s_m12 {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .M12) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M12 ≃* Spor .M12 := b
  refine k150s_row_of_not_dvd (hJ.not_dvd ?_ ?_) <;>
  · rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
    norm_num

theorem k150s_j1 {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .J1) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J1 ≃* Spor .J1 := b
  refine k150s_row_of_not_dvd (hJ.not_dvd ?_ ?_) <;>
  · rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J1.card_J1]
    norm_num

theorem k150s_j3 {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .J3) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J3 ≃* Spor .J3 := b
  refine k150s_row_of_not_dvd (hJ.not_dvd ?_ ?_) <;>
  · rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J3.card_J3]
    norm_num

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
