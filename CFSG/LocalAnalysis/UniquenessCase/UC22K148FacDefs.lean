module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G]

@[expose] def IsFactor148 (H : Subgroup G) : Prop :=
  IsComponentOf H ⊤ ∨ Nonempty (↥H ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (↥H ≃* Equiv.Perm (Fin 5))

variable (G) in
@[expose] def HasFactors148 : Prop :=
  ∃ (m : ℕ) (Hs : Fin m → Subgroup G), IsInternalDirect ⊤ Hs ∧ ∀ i, IsFactor148 (Hs i)

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
