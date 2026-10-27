module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45RadGen
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45Inner
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45Outer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)

theorem Sp44.g45Body_Psub : G45Body Sp44.S4 Sp44.Psub :=
  ⟨Sp44.Q1sub, Sp44.Q2sub, Sp44.br2TwoRadicals_Psub, fun A hel h8 => by
    by_cases hin : A ≤ innAutOf Sp44.S4
    · exact Or.inr (Or.inr ⟨hin, Sp44.inner_case A hel h8 hin⟩)
    · exact Or.inl (Sp44.outer_case A hel h8 hin)⟩

theorem finG45Sp44_holds : FinG45Sp44 :=
  finG45Sp44_of_body (fun M _ hM τ hτ => sp44_dynkin_generates M hM τ hτ)
    (fun M _ hM P hP => by
      obtain ⟨e⟩ := Sp44.isSp4_equiv_S4 hM
      exact g45Body_of_sylow e hP Sp44.Psub_sylow Sp44.g45Body_Psub)

end CFSG.LocalAnalysis.WeakClosure81

end
