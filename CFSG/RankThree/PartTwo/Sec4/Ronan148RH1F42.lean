module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Shape
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFF4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.HardMathSupport.Dickson.Bal207.FamF42 (F42CompType compShape_F4_two)

theorem not_isA5Type_of_f42CompType : ∀ (Q : Type) [Group Q], F42CompType Q → ¬ IsA5Type Q := by
  intro Q _ ⟨F, _, _, hF, ⟨f⟩⟩ hA5
  have h1 := hA5.card
  rw [Nat.card_congr f.toEquiv, RonanK429F.F4.card_statedSp_quot hF] at h1
  norm_num at h1

section F42


theorem noCfgS427_adjointF4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    [Finite ↥(adjointGroup Tag.F4 K)] : NoCfgS427 ↥(adjointGroup Tag.F4 K) :=
  noCfgS427_of_compShape not_isA5Type_of_f42CompType fun β h3 h1 => compShape_F4_two hK β h3 h1



theorem rowOf427_f42
    :
    RowOf427 (TauCeti.CFSGIndex.lie CFSG.Assembly.RankThreeEven.f4TwoIndex).Group := by
  refine rowOf427_of_noCfgS fun S _ _ _ _ ⟨e⟩ => ?_
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := Item434F42.exists_model e
  haveI : Finite (adjointGroup ReeTag.F4.tag K) := Finite.of_equiv S φ.toEquiv
  have hG : Nat.card (adjointGroup ReeTag.F4.tag K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hK] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  refine ⟨NoCfgS427.of_mulEquiv φ (noCfgS427_adjointF4 hK), noONS427_of_card ?_⟩
  rw [Nat.card_congr φ.toEquiv, hG]
  norm_num

end F42

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
