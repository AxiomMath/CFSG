module

public import CFSG.RankThree.OddKernel.SporadicKernelCases
public import CFSG.Sporadic.J4

public section

namespace CFSG.RankThree.OddKernel

open CFSG.SectionRank CFSG.Blueprint

theorem j4OrderHyp : J4OrderHyp := by
  show Nat.card NativeSporadic.J4 ∣ 86775571046077562880
  rw [CFSG.Sporadic.J4.card_J4]

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {S : Type} [Group S]

theorem ker_eq_bot_of_isSporadic_J4 (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .J4) : π.ker = ⊥ := by
  obtain ⟨e⟩ := h
  exact ker_eq_bot_of_mulEquiv_cover π hπ hC h6 e fun π' h1 h2 h3 =>
    J4_perfect_odd_cover_trivial j4OrderHyp π' h1 h2 h3

end CFSG.RankThree.OddKernel
