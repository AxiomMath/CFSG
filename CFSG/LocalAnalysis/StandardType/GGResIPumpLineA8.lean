module

public import CFSG.LocalAnalysis.StandardType.GGTwAutHolds
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem largeEvenLabelAll_A8_autCardSC {f : ℕ} (h3 : 3 ∣ 2 ^ f + 1) :
    LargeEvenLabelAll ⟨.A, 8, f⟩ fun R _ I _ =>
      GGTorusAutCardSC 3 R I 4 384 := by
  have h8 : 2 * 4 - 1 + 1 = 8 := by norm_num
  have h384 : 2 ^ 4 * Nat.factorial 4 = 384 := by norm_num
  simpa only [h8, h384] using
    ggTwSL_label (r := 4) (f := f) (by norm_num) h3 1

theorem largeEvenLabelAll_A8_notDvdSCJ {f : ℕ} (h3 : 3 ∣ 2 ^ f + 1)
    (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.A, 8, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 4 27 :=
  LargeEvenLabelAll.mono (fun R _ I _ hSC =>
    GGTorusAutCardSC.notDvdSCJ (labJ := labJ) hSC (by norm_num))
    (largeEvenLabelAll_A8_autCardSC h3)

end CFSG.StandardType

end
