module

public import CFSG.RankThree.PartTwo.Sec11.Item116H3KFact
public import CFSG.RankThree.PartTwo.KFacts.K71Item119

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent

theorem isoLThreeMinusPi_fixedSub {m : ℕ} (hm : 1 ≤ m) {X : Type} [Group X] [Finite X]
    (hX : Sec8.IsoLThreeMinusPi X 2 (3 * m)) {α : MulAut X} (hα : orderOf α = 3)
    (hαi : α ∉ (MulAut.conj : X →* MulAut X).range) :
    Sec8.IsoLThreeMinusPi (Sec11.fixedSub α) 2 m := by
  have hα3 : α ^ 3 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  exact KFacts.isoLThreeMinusPi_eqLocus hm hX hα3 hαi

end CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent
