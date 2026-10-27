module

public import CFSG.LocalAnalysis.StandardType.GGKGASp
public import CFSG.LocalAnalysis.StandardType.GGTwOmPlusHolds
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_C4_notDvdSCJ
    (n : ℕ)
    (hn : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1) (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.C, 4, n⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 27 := by
  have hsq : 3 ∣ (2 ^ n) ^ 2 - 1 := by
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ n) 1
    rw [hfac]
    rcases hn with h | h
    · exact dvd_mul_of_dvd_left h _
    · exact dvd_mul_of_dvd_right h _
  have h384 : 2 ^ 4 * Nat.factorial 4 = 384 := by norm_num
  have hC4 : LargeEvenLabelAll ⟨.C, 4, n⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I 4 384 := by
    have h := KGA.kga_label (p := 3) (f := n) (N := 4) Nat.prime_three (by norm_num)
      (by norm_num) hsq
    simpa only [h384] using h
  exact LargeEvenLabelAll.mono (fun R _ I _ hSC =>
    GGTorusAutCardSC.notDvdSCJ (labJ := labJ) hSC (by norm_num)) hC4

theorem largeEvenLabelAll_D5_notDvdSCJ
    (n : ℕ)
    (hn : 3 ∣ 2 ^ n + 1) (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.D, 5, n⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 27 := by
  have h384 : 2 ^ 4 * Nat.factorial 4 = 384 := by norm_num
  have hD5 : LargeEvenLabelAll ⟨.D, 5, n⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I 4 384 := by
    have h := ggTwOmPlus_label (r := 4) (f := n) (by norm_num) (by norm_num) hn
    simpa only [h384] using h
  exact LargeEvenLabelAll.mono (fun R _ I _ hSC =>
    GGTorusAutCardSC.notDvdSCJ (labJ := labJ) hSC (by norm_num)) hD5

end CFSG.StandardType

end
