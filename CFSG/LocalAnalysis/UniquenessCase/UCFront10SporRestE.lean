module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRestB
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporSuz
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi22

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

@[expose] def K105SporRestE : Prop :=
  ∀ s ∈ ([.ONan, .Co1, .Fi23, .Fi24Prime, .HN, .Ly, .Th, .B, .M] :
    List TauCeti.SporadicName), K105SporAt s

theorem k105SporRestB_of_restE
    (h : K105SporRestE) :
    K105SporRestB := by
  intro s hs
  cases s
  case Suz => exact k105SporAt_Suz
  case Co2 => exact k105SporAt_Co2
  case Fi22 => exact k105SporAt_Fi22
  all_goals first
    | exact h _ (by decide)
    | exact absurd hs (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
