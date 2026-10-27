module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRest
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporJ3
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporMcL
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

@[expose] def K105SporRestB : Prop :=
  ∀ s ∈ ([.Suz, .ONan, .Co1, .Co2, .Fi22, .Fi23, .Fi24Prime, .HN, .Ly, .Th, .B, .M] :
    List TauCeti.SporadicName), K105SporAt s

theorem k105SporRest_of_restB
    (h : K105SporRestB) :
    K105SporRest := by
  intro s hs
  cases s
  case J3 => exact k105SporAt_J3
  case McL => exact k105SporAt_McL
  case Co3 => exact k105SporAt_Co3
  all_goals first
    | exact h _ (by decide)
    | exact absurd hs (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
