module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporMathieu
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporLat
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporJ4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

@[expose] def K105SporRest : Prop :=
  ∀ s ∈ ([.J3, .McL, .Suz, .ONan, .Co1, .Co2, .Co3, .Fi22, .Fi23, .Fi24Prime, .HN, .Ly, .Th, .B,
    .M] : List TauCeti.SporadicName), K105SporAt s

theorem k105Spor_of_rest
    (h : K105SporRest) : K105Spor := by
  refine k105Spor_of_forall fun s hs => ?_
  cases s
  case J1 => exact absurd rfl hs
  case M11 => exact k105SporAt_M11
  case M12 => exact k105SporAt_M12
  case M22 => exact k105SporAt_M22
  case M23 => exact k105SporAt_M23
  case M24 => exact k105SporAt_M24
  case J2 => exact k105SporAt_J2
  case J4 => exact k105SporAt_J4
  case HS => exact k105SporAt_HS
  case He => exact k105SporAt_He
  case Ru => exact k105SporAt_Ru
  all_goals exact h _ (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
