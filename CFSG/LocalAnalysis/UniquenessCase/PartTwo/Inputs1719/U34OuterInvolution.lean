module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_U34OuterInv : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsU3 Q 2 →
    ∀ σ : MulAut Q, σ * σ = 1 → σ ∉ (MulAut.conj : Q →* MulAut Q).range →
      ∃ x : Q, orderOf x = 5 ∧ σ x = x⁻¹ ∧
        ∀ τ : MulAut Q, τ * σ = σ * τ → τ x ∈ Subgroup.zpowers x

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
