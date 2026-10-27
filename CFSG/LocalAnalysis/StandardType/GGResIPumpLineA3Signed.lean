module

public import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem largeEvenLabelAll_A7_autCard (n : ℕ) (h3 : 3 ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.A, 7, n⟩ fun R _ I _ => GGTorusAutCardSC 3 R I 4 384 := by
  have h := ggTwSL_label (r := 4) (f := n) (by norm_num) h3
  have h784 : 2 * 4 - 1 = 7 := by norm_num
  have h384 : 2 ^ 4 * Nat.factorial 4 = 384 := by norm_num
  simpa only [h784, h384] using h

theorem largeEvenLabelAll_twD5_autCard
    (n : ℕ) (hn : 1 ≤ n)
    (h3 : 3 ∣ 2 ^ n - 1) :
    LargeEvenLabelAll ⟨.twD, 5, n⟩ fun R _ I _ => GGTorusAutCardSC 3 R I 4 384 := by
  have h := ggTwOm_label (r := 4) (f := n) hn (by norm_num) (Or.inl h3)
  have h45 : 4 + 1 = 5 := by norm_num
  have h384 : 2 ^ 4 * Nat.factorial 4 = 384 := by norm_num
  simpa only [h45, h384] using h

theorem largeEvenLabelAll_A7_notDvdSCJ (n : ℕ) (h3 : 3 ∣ 2 ^ n + 1)
    (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.A, 7, n⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 27 :=
  LargeEvenLabelAll.mono (fun R _ I _ hSC =>
    GGTorusAutCardSC.notDvdSCJ (labJ := labJ) hSC (by norm_num))
    (largeEvenLabelAll_A7_autCard n h3)

theorem largeEvenLabelAll_twD5_notDvdSCJ
    (n : ℕ) (hn : 1 ≤ n)
    (h3 : 3 ∣ 2 ^ n - 1) (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.twD, 5, n⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 27 :=
  LargeEvenLabelAll.mono (fun R _ I _ hSC =>
    GGTorusAutCardSC.notDvdSCJ (labJ := labJ) hSC (by norm_num))
    (largeEvenLabelAll_twD5_autCard (n := n) hn h3)

end CFSG.StandardType

end
