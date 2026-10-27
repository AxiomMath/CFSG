module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.Timmesfeld75.Dihedral
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem card_eq_two_pow_of_pRank_eq {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (hA : IsElemAbelian 2 A) {n : ℕ} (h : CFSG.pRank 2 ↥A = n) : Nat.card A = 2 ^ n := by
  haveI : CFSG.IsElementaryAbelian 2 ↥A := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hA
  obtain ⟨k, hk⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥A).exists_card_eq
  rw [CFSG.pRank_eq_of_card_eq_pow one_lt_two hk] at h
  rw [h] at hk
  exact hk

end CFSG.LocalAnalysis.WeakClosure81
