module

public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResHolds
public import CFSG.RankThree.PartTwo.Sec15.Ronan152OmegaNe
public import CFSG.RankThree.PartTwo.Sec14.Item1411_3RHolds

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec11
  CFSG.RankThree.PartTwo.Sec6 CFSG.RankThree.PartTwo.Sec4


theorem step152SL25OneOmegaR_of_155w
    (h155 : Item155wJ2R) : Step152SL25OneOmegaR := by
  intro G _ _ A c L hR hHJ M X hctx B b d Lb hB hc hcent hΩ
  have h142 : Item142AllS14 := item142AllS14_holds
  have h134 : Item134 := item134_holds
  have h48 : Sec4.Item4_8 := CFSG.RankThree.PartTwo.Sec11.Close.closed_sec4Item4_8
  have h425 : Sec4.Item4_25Fix := Sec4.Ronan148S.item4_25Fix_holds
  have h41 : Sec4.Item4_1LargePrime := Sec4.diag_item41LargePrime_holds
  have hGW : Sec6.GWLBalanceStatement := Sec6.gwlBalanceStatement_holds
  have h148 : Item148R := Sec14.Ronan148M.item148R_holds
  have hbot : Item145BotS14 := Sec14.Ronan149.item145BotS14_holds
  have hcomp : Step143HJCompOne :=
    Sec14.Ronan148D.step143HJCompOne_of_item4_25Fix' h425 h134 h48 h41 hGW
  have hlist : Step1515HJListLe := step1515HJListLe_of h148 hbot h134 h48
  exact step152SL25OneOmegaR_of_items h142 h134 h48 hcomp hlist h155
    G A c L hR hHJ M X hctx B b d Lb hB hc hcent hΩ

theorem y4CoreExclSL25HJR_of_155w
    (h155 : Item155wJ2R) (hloc : Claim1411LocalR)
    (h152 : Item152BigR) (h153 : Item153MainJ2R) : Y4CoreExclSL25HJR :=
  y4CoreExclSL25HJR_of_oneOmega_big (step152SL25OneOmegaR_of_155w h155)
    item142AllS14_holds Sec4.Ronan148S.item4_25Fix_holds item134_holds
    CFSG.RankThree.PartTwo.Sec11.Close.closed_sec4Item4_8 Sec4.diag_item41LargePrime_holds
    Sec6.gwlBalanceStatement_holds Sec14.Ronan148M.item148R_holds
    Sec14.Ronan149.item145BotS14_holds hloc h152 h153 h155

end CFSG.RankThree.PartTwo.Sec15
