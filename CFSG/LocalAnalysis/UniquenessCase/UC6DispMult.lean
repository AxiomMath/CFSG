module

public import CFSG.LocalAnalysis.UniquenessCase.UC6P6a
public import CFSG.LocalAnalysis.UniquenessCase.UC6A10Aut
public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

@[expose] def KMultL2 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J →
    ∀ (N : Subgroup J) [N.Normal], N ≤ center J →
      (∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ CFSG.Blueprint.LieModel (J ⧸ N) .PSL 2 r 2) →
      Odd (Nat.card (center J)) → center J = ⊥

section Derive


theorem kMultList620_of_kMultL2 (h : KMultL2) : KMultList620 := by
  intro J _ _ hq N _ hN hlist hodd
  rcases hlist with hL2 | hT | hA
  · exact h J hq N hN hL2 hodd
  · exact kMult_Tits J hq N hN hT hodd
  · exact kMult_A10 J hq N hN hA hodd

end Derive

end CFSG.LocalAnalysis.UniquenessCase.UCK
