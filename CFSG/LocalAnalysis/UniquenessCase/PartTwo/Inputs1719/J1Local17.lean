module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_J1A5Gen : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsJ1 X →
    ∀ S : Subgroup (MulAut X), IsPGroup 2 S →
      ∃ Δ : Finset (Subgroup X),
        Δ.Nonempty ∧
          (∀ A ∈ Δ, IsAlt ↥A 5 ∧ ∀ s ∈ S, A.map s.toMonoidHom = A) ∧
            (⨆ A ∈ Δ, A) = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
