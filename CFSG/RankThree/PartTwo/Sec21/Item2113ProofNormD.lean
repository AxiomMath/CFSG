module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.KFacts.KP14Monomial

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

theorem mem_normalizer_of_map_le [Finite G] {w : G} {X : Subgroup G}
    (h : X.map (MulAut.conj w).toMonoidHom ≤ X) : w ∈ Subgroup.normalizer (X : Set G) := by
  have heq : X.map (MulAut.conj w).toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge h
      (by rw [Subgroup.card_map_of_injective (MulAut.conj w).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      exact mul_left_cancel (mul_right_cancel hyx)
    exact this ▸ hy

end CFSG.RankThree.PartTwo.Sec21.Item2113Proof
