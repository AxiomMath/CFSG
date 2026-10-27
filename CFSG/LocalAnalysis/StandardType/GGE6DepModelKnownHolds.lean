module

public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggE6DepModelProp_of_scr {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGE6ThreeModelSCr R I) : GGE6DepModelProp R I := by
  intro L' _ _ ψ A hTB _
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, -, hsc⟩ := hTB
  exact h L' ψ hψ hker hperf A hA hAI hr hsc

section Certs33


theorem ggE6DepModelKnown_of_model (hM : GGE6ThreeModelInput) : GGE6DepModelKnown := by
  intro lab hlab hΛ
  rcases hlab with ⟨htag, h3⟩ | ⟨htag, h3⟩
  · have key := largeEvenLabelAll_e6Div_of (P := fun R _ I => GGE6DepModelProp R I) htag hΛ h3
      (fun K _ _ n hn hK h3' => ggE6DepModelProp_of_scr (hM.1 K n hn hK h3'))
    exact LargeEvenLabelAll.mono (fun R _ I F h _ _ => h.2) key
  · exact TwE6Delta.labelAll htag
      (Q := fun R _ I => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGE6DepModelProp R I)
      (fun K _ _ hK _ _ => ggE6DepModelProp_of_scr (hM.2 K lab.n hΛ.1 hK h3))

end Certs33

section CertsModel


theorem ggE6DepModelKnown_holds : GGE6DepModelKnown :=
  ggE6DepModelKnown_of_model E6ThreeModel.e6ThreeModel_holds

end CertsModel

end CFSG.StandardType

end
