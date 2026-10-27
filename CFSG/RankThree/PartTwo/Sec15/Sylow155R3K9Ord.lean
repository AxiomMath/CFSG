module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Core
import CFSG.Sporadic.Bridge.HSSurj
import CFSG.Sporadic.Bridge.J1
import CFSG.Sporadic.Bridge.J3Surj
import CFSG.Sporadic.Bridge.J4Surj
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.M23Surj
import CFSG.Sporadic.Bridge.M24Surj
import CFSG.Sporadic.Bridge.ONSurj
import CFSG.Sporadic.J1
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M22
import CFSG.Sporadic.ON
public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.RankThree.PartTwo.Sec4 (Spor)

theorem rowOfK9_m11 :
    RowOfK9 (Spor .M11) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M11 ≃* Spor .M11 := b
  refine rowOfK9_of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M11]
  norm_num

theorem rowOfK9_m12 : RowOfK9 (Spor .M12) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M12 ≃* Spor .M12 := b
  refine rowOfK9_of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
  norm_num

theorem rowOfK9_m22 : RowOfK9 (Spor .M22) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M22 ≃* Spor .M22 := b
  refine rowOfK9_of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
  norm_num

theorem rowOfK9_m23 :
    RowOfK9 (Spor .M23) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M23 ≃* Spor .M23 := b
  refine rowOfK9_of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Schreier.m23_card]
  norm_num

theorem rowOfK9_m24 :
    RowOfK9 (Spor .M24) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M24 ≃* Spor .M24 := b
  refine rowOfK9_of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M24]
  norm_num

theorem rowOfK9_j1 : RowOfK9 (Spor .J1) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J1 ≃* Spor .J1 := b
  refine rowOfK9_of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J1.card_J1]
  norm_num

theorem rowOfK9_j3 :
    RowOfK9 (Spor .J3) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J3 ≃* Spor .J3 := b
  refine rowOfK9_of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J3.card_J3]
  norm_num

theorem rowOfK9_j4 :
    RowOfK9 (Spor .J4) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J4 ≃* Spor .J4 := b
  refine rowOfK9_of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J4.card_J4]
  norm_num

theorem rowOfK9_hs :
    RowOfK9 (Spor .HS) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.HS ≃* Spor .HS := b
  refine rowOfK9_of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.HS.card_HS]
  norm_num

theorem rowOfK9_on :
    RowOfK9 (Spor .ONan) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.ON ≃* Spor .ONan := b
  refine rowOfK9_of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.ON.card_ON]
  norm_num

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
