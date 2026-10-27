module

public import CFSG.LocalAnalysis.StandardType.GGResILineAutBound
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Aut
public import CFSG.LocalAnalysis.StandardType.GGPumpTwExcKnownHolds
public import CFSG.LocalAnalysis.StandardType.GGTableB
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggResILineBThreeExc_F4
    (labJ : LargeEvenLabel) {f : ℕ} :
    LargeEvenLabelAll ⟨.F4, 0, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 4 5 := by
  have hfacts := largeEvenLabelAll_and (KGA.ggF4_basics_label (f := f))
    (KGA.ggF4_autOrder_label (p := 3) (f := f) Nat.prime_three (by norm_num))
  have hfacts0 : LargeEvenLabelAll ⟨.F4, 0, f⟩ fun R _ I _ =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ GGHasLabel ⟨.F4, 4, f⟩ R ∧
        (∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r)) ∧ KGA.GGF4AutOrderAt 3 R := by
    change LargeEvenLabelAll ⟨.F4, 4, f⟩ fun R _ I _ =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ GGHasLabel ⟨.F4, 4, f⟩ R ∧
        (∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r)) ∧ KGA.GGF4AutOrderAt 3 R
    exact hfacts
  refine hfacts0.mono ?_
  rintro R _ I _ ⟨⟨hsimple, hnab, _hlab, hinn⟩, hAO⟩
  have hZ : Subgroup.center R = ⊥ :=
    @center_eq_bot_of_isSimpleGroup_of_nonabelian R _ hsimple hnab
  have hI : GGOutdiagPrime 3 R I := by
    intro φ hφ _
    obtain ⟨r, hr⟩ := hinn φ hφ
    exact ⟨r, hr.symm⟩
  exact GGTorusAutNotDvdSCJ_of_exact_order_1152 fun L' _ _ ψ hψ hker hperf A hA hAI h81 _ =>
    ggPumpTwExc_transport hZ hI hAO ψ hψ hker hperf A hA hAI h81

theorem ggResILineBThreeExc_E6
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.E6, 0, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 4 5 := by
  have hknown : GGPumpTwExcKnown := ggPumpTwExcKnown_holds
  refine (hknown f hf ⟨.E6, 0, f⟩ (Or.inl ⟨rfl, h3⟩)).mono ?_
  rintro R _ I _ ⟨-, -, horder⟩
  exact GGTorusAutNotDvdSCJ_of_exact_order_1152 fun L' _ _ ψ hψ hker hperf A hA hAI h81 hsc =>
    horder L' ψ hψ hker hperf A hA hAI h81 hsc

theorem ggResILineBThreeExc_twE6
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f - 1) (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.twE6, 0, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 4 5 := by
  have hknown : GGPumpTwExcKnown := ggPumpTwExcKnown_holds
  refine (hknown f hf ⟨.twE6, 0, f⟩ (Or.inr ⟨rfl, h3⟩)).mono ?_
  rintro R _ I _ ⟨-, -, horder⟩
  exact GGTorusAutNotDvdSCJ_of_exact_order_1152 fun L' _ _ ψ hψ hker hperf A hA hAI h81 hsc =>
    horder L' ψ hψ hker hperf A hA hAI h81 hsc

end CFSG.StandardType

end
