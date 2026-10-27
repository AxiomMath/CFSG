module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] [Finite G]

private theorem HasQuotShape.mono' {K : Subgroup G} {N : Set G}
    {P Q : ∀ (X : Type) [Group X], Prop} (h : HasQuotShape K N P)
    (hPQ : ∀ (X : Type) [Group X], P X → Q X) : HasQuotShape K N Q := by
  obtain ⟨X, hX, φ, hφ, hker, hP⟩ := h
  exact ⟨X, hX, φ, hφ, hker, hPQ X hP⟩

end CFSG.LocalAnalysis.WeakClosure81

end
