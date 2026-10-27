module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

@[expose] def s16h_e3_R920L28 (D : Data G) : Prop :=
  3 ∈ D.sig → ∀ L₀ D₃ A : Subgroup G, L₀ ∈ calC D.M → L₀ ≤ D.M → IsL2 (Bar2 L₀) 3 →
    pCoreOf 2 L₀ ≠ ⊥ → D₃ ≤ L₀ → Nat.card D₃ = 3 → D₃ ∈ uniqueSet D.M →
    A ≤ L₀ → Nat.card A = 7 → A ∈ uniqueSet D.M → UniqueMax D.M L₀

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
