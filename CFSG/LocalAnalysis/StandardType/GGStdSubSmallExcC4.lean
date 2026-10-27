module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcSplit
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC12

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly

theorem excFieldLabel_field {p : ℕ} {lab : LargeEvenLabel} (h : ExcFieldLabel p lab) :
    GGIOneMoreFieldLabel p lab :=
  Or.inr (Or.inr h)

section Field


theorem largeEvenLabelAll_innerSmall_excField {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : ExcFieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I := by
  rcases h with ⟨htag, hpn, hp3, -⟩ | ⟨htag, hpn, -⟩
  · exact SmallExcC12.largeEvenLabelAll_innerSmall_e6Tag hp hlab htag hpn hp3
  · exact SmallExcC12.largeEvenLabelAll_innerSmall_excTag hp hlab htag hpn

theorem largeEvenLabelAll_excField_innerSmall {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : ExcFieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ((∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I :=
  largeEvenLabelAll_and (largeEvenLabelAll_and
    (largeEvenLabelAll_innerDiagBound_field hp hlab (excFieldLabel_field h))
    (IOneMore.largeEvenLabelAll_normAbove_field hp hlab (excFieldLabel_field h)))
    (largeEvenLabelAll_innerSmall_excField hp hlab h)

theorem ggStdSubSmallInputOn_excField : GGStdSubSmallInputOn ExcFieldLabel :=
  ggStdSubSmallInputOn_of_labels_innerSmall ggLNoncyclicInput_holds fun _ _ hp hlab h _ =>
    largeEvenLabelAll_excField_innerSmall hp hlab h

end Field

end CFSG.StandardType.SmallExc

end
