module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfKG
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxCount
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxFixedRoot

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Tags


theorem ggExcHalfMaxElemInput_of_tag {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    (h3 : BigElemAbelianToralBar τ 3) (h5 : BigElemAbelianToralBar τ 5) :
    GGExcHalfMaxElemInput τ := by
  intro K _ _ _ p hp hp2 hpq hp35 E hE hcard hSC
  have hbar : BigElemAbelianToralBar τ p := by
    rcases hp35 with rfl | rfl
    · exact h3
    · exact h5
  exact card_ge_of_toral hτ hp hp2 hbar (halfMaxFixedRoot_E7_E8 hτ hp hp2) K hpq E hE hcard hSC

theorem ggExcHalfMaxElemInput_E7 (h3 : BigElemAbelianToralBar .E7 3)
    (h5 : BigElemAbelianToralBar .E7 5) : GGExcHalfMaxElemInput .E7 :=
  ggExcHalfMaxElemInput_of_tag (Or.inl rfl) h3 h5

theorem ggExcHalfMaxElemInput_E8 (h3 : BigElemAbelianToralBar .E8 3)
    (h5 : BigElemAbelianToralBar .E8 5) : GGExcHalfMaxElemInput .E8 :=
  ggExcHalfMaxElemInput_of_tag (Or.inr rfl) h3 h5

end Tags

end ExcFramesHalf

end CFSG.StandardType
