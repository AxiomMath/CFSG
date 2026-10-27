module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenFive
public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwoBridge
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.WeakClosure81.W15Two
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Certified

theorem NamedInputs15.of_inputs (hB : Asc80ThmB) (hM : SchurMultiplierInput)
    (h86 : W3Lem86_1Two G) : NamedInputs15 G :=
  ⟨hB, hM, w3Lem122Two_holds, h86, w15Thm145_holds G⟩

theorem Inputs15Two.of_inputs (hB : Asc80ThmB) (hM : SchurMultiplierInput)
    (h86 : W3Lem86_1Two G) (hdich : W15Eleven3Dich G) (hs4 : W15Eleven3S4 G)
    (hbar : W15Eleven4Bar G) : Inputs15Two G :=
  ⟨NamedInputs15.of_inputs hB hM h86, hdich, hs4, hbar⟩

end Certified

end CFSG.LocalAnalysis.WeakClosure81
