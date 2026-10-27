module

public import CFSG.RankThree.PartOne.KS.LyFiveX
public import CFSG.RankThree.Native.LyFiveLocal

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly CFSG.RankThree.Native Subgroup

theorem centralizer_xJ_eq
    (hle : Nat.card (Subgroup.centralizer ({lyFiveXJ} : Set J)) ≤ 2340000) :
    Subgroup.centralizer ({lyFiveXJ} : Set J) = fiveU lyFiveAJ lyFiveBJ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -, h13, -, -, h16, -, -, -⟩ :=
    lyFiveMRelJ.local_structure lyFiveCertJ
  have hU : Nat.card (fiveU lyFiveAJ lyFiveBJ) = 2250000 := by omega
  have hsub : fiveU lyFiveAJ lyFiveBJ ≤ Subgroup.centralizer ({lyFiveXJ} : Set J) := by
    rw [h13]; exact inf_le_left
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hsub
  have hpos : 0 < Nat.card (Subgroup.centralizer ({lyFiveXJ} : Set J)) := Nat.card_pos
  have hk1 : k = 1 := by
    rw [hU] at hk
    have hk0 : k ≠ 0 := by rintro rfl; omega
    have : k < 2 := by omega
    omega
  rw [hU, hk1, mul_one] at hk
  exact (Subgroup.eq_of_le_of_card_ge hsub (by omega)).symm

theorem card_centralizer_xJ_eq
    (hC : Subgroup.centralizer ({lyFiveXJ} : Set J) = fiveU lyFiveAJ lyFiveBJ) :
    Nat.card (Subgroup.centralizer ({lyFiveXJ} : Set J)) = 2250000 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -, h13, -, -, h16, -, -, -⟩ :=
    lyFiveMRelJ.local_structure lyFiveCertJ
  rw [hC]
  omega

theorem fiveCoreAt'_xJ
    (hC : Subgroup.centralizer ({lyFiveXJ} : Set J) = fiveU lyFiveAJ lyFiveBJ) :
    FiveCoreAt' lyFiveXJ := by
  obtain ⟨-, -, -, -, -, -, h7, -, -, -, -, -, -, -, -, -, h17, h18, h19⟩ :=
    lyFiveMRelJ.local_structure lyFiveCertJ
  have hxQ : lyFiveXJ ∈ fiveQ lyFiveXJ lyFiveVJ := FiveQRel.x_mem
  exact fiveCoreAt'_of_normal_sub (T := J) (w := lyFiveXJ) (Q := fiveQ lyFiveXJ lyFiveVJ)
    (U := fiveU lyFiveAJ lyFiveBJ) hC h17 h18
    (IsPGroup.of_card (n := 5) (by rw [h7]; norm_num))
    (by rw [h19]; exact Subgroup.zpowers_le.2 hxQ)

theorem fiveCoreAt'_xJ_of_checks
    (hB : lyXClassOK = true) : FiveCoreAt' lyFiveXJ :=
  fiveCoreAt'_xJ (centralizer_xJ_eq (card_centralizer_xJ_le hB))

theorem card_centralizer_xJ_eq_of_checks
    (hB : lyXClassOK = true) :
    Nat.card (Subgroup.centralizer ({lyFiveXJ} : Set J)) = 2250000 :=
  card_centralizer_xJ_eq (centralizer_xJ_eq (card_centralizer_xJ_le hB))

end CFSG.RankThree.PartOne.LyFive
