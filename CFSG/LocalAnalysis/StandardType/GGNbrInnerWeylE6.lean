module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6Split
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoSeven

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrWeylE6TwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .E6 ∧ lab.n = 1 ∧ (p = 3 ∨ p = 7)

theorem ggNbrWeylE6Label_cases {p : ℕ} {lab : LargeEvenLabel} (h : GGNbrWeylE6Label p lab) :
    GGNbrWeylE6TwoLabel p lab ∨ GGNbrWeylE6ThreeDvdLabel p lab := by
  obtain ⟨hpow, ht, ⟨hp3, hdvd⟩ | ⟨hn1, hp37⟩⟩ := h
  · exact Or.inr ⟨hpow, ht, hp3, hdvd⟩
  · exact Or.inl ⟨hpow, ht, hn1, hp37⟩

section Main

theorem largeEvenLabelAll_noLine_e6_two {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .E6 ∧ lab.n = 1 ∧ (p = 3 ∨ p = 7)) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∃ r, (GGTorusLift p r R ∨ r = 0) ∧ GGTorusNoLine p r R I := by
  obtain ⟨htag, hn1, hp37⟩ := h
  rcases hp37 with rfl | rfl
  · exact largeEvenLabelAll_torusLift_noLine_e6_two_three hlab ⟨htag, hn1⟩
  · exact largeEvenLabelAll_noLine_e6_two_seven_or hlab ⟨htag, hn1⟩

theorem ggNbrInnerWeylOn_e6Two : GGNbrInnerWeylOn GGNbrWeylE6TwoLabel :=
  ggNbrInnerWeylOn_of_labels fun p lab hp hp2 hlab ⟨hpow, ht, hn1, hp37⟩ =>
    largeEvenLabelAll_weylInnerKLevel_of_noLine_or
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow)
      (largeEvenLabelAll_noLine_e6_two hlab ⟨ht, hn1, hp37⟩)

end Main

end CFSG.StandardType

end
