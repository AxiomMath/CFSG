module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsOrders
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionL44
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionSp64
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionU58
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp f4TwoIndex)

theorem rowSEpsOf_eight_SL4 : RowSEpsOf (projSL 4 (GaloisField 2 2)) := by
  refine fun S _ _ _ _ ⟨e⟩ => ?_
  have hX : Nat.card (projSL 4 (GaloisField 2 2)) = 3 ^ (3 + 1) * 12185600 :=
    (Nat.card_congr KS21.L44.equivSL.toEquiv).trans KS21.L44.card_M_eq
  have hS : Nat.card S = 3 ^ (3 + 1) * 12185600 := (Nat.card_congr e.toEquiv).trans hX
  exact noCfgSEps_of_card (N := 3 ^ (3 + 1) * 12185600) (B := 3) hS.dvd (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_eight_Sp6_4 : RowSEpsOf (projSp 3 (GaloisField 2 2)) := by
  refine fun S _ _ _ _ ⟨e⟩ => ?_
  have hX : Nat.card (projSp 3 (GaloisField 2 2)) = 3 ^ (3 + 1) * 50692096000 :=
    (Nat.card_congr KS21.Sp64.equivSp.toEquiv).trans KS21.Sp64.card_Sp_eq
  have hS : Nat.card S = 3 ^ (3 + 1) * 50692096000 := (Nat.card_congr e.toEquiv).trans hX
  exact noCfgSEps_of_card (N := 3 ^ (3 + 1) * 50692096000) (B := 4) hS.dvd (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_eight_SU5_4 : RowSEpsOf (projSU 5 2 2) := by
  refine fun S _ _ _ _ ⟨e⟩ => ?_
  have hS : Nat.card S = 3 ^ 2 * 5938216960000 :=
    (Nat.card_congr e.toEquiv).trans Item434SmallTwoOther.U54.card_U54
  exact noCfgSEps_of_card (N := 3 ^ 2 * 5938216960000) (B := 4) hS.dvd (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_eight_SU5_8 : RowSEpsOf (projSU 5 2 3) := by
  refine fun S _ _ _ _ ⟨e⟩ => ?_
  have hX : Nat.card (projSU 5 2 3) = 3 ^ (8 + 1) * 236583028271349760 :=
    (Nat.card_congr KS21.U58.equivSUI.toEquiv).trans KS21.U58.card_SUI
  have hS : Nat.card S = 3 ^ (8 + 1) * 236583028271349760 := (Nat.card_congr e.toEquiv).trans hX
  exact noCfgSEps_of_card (N := 3 ^ (8 + 1) * 236583028271349760) (B := 8) hS.dvd (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree in
theorem rowSEpsOf_eight_F4 :
    RowSEpsOf (TauCeti.CFSGIndex.lie f4TwoIndex).Group := by
  refine fun S _ _ _ _ ⟨e⟩ => ?_
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 CFSG.Assembly.RankThreeEven.primePowerTwo
    CFSG.Assembly.RankThreeEven.f4TwoIndex.2 rfl e
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hmodel
  have hK2 : Nat.card K = 2 := hK
  have hG : Nat.card (adjointGroup ReeTag.F4.tag K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hK2] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  have hS : Nat.card S = 3311126603366400 := (Nat.card_congr φ.toEquiv).trans hG
  exact noCfgSEps_of_card (N := 3311126603366400) (B := 5) hS.dvd (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

end CFSG.RankThree.PartTwo.Sec4.RonanEps
