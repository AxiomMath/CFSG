module

public import CFSG.RankThree.PartOne.KP.SporadicRank
public import CFSG.RankThree.PartOne.KS.Co2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
import CFSG.Sporadic.Schreier.J4SCatalog
import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartOne.SPOR.OuterB
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.SporadicSchreierDispatch
  (SporadicSchreierCase sporadicSchreierCase_of_outer)
open CFSG.ComponentClassification.CatalogSchreierCases

namespace CFSG.RankThree.PartOne.SPOR

theorem sporadicCoprimeRankData_holds :
    SporadicCoprimeRankData where
  hn := sporadicCoprimeRank_of_card_outer_le (k := 2) (by norm_num) card_outer_HN.le
  ly := sporadicCoprimeRank_of_card_outer_le (k := 2) (by norm_num)
    (by rcases card_outer_Ly with h | h <;> omega)
  th := sporadicCoprimeRank_of_card_outer_le (k := 1) (by norm_num) card_outer_Th.le

theorem co2AllInner_holds :
    Co2AllInner :=
  CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner

theorem sporadicSchreierCase_of_card_eq_one_or_two {s : TauCeti.SporadicName}
    (h : Nat.card (Outer (NativeSporadic.Carrier s)) = 1 ∨
      Nat.card (Outer (NativeSporadic.Carrier s)) = 2) : SporadicSchreierCase s :=
  sporadicSchreierCase_of_outer (isSolvable_of_card_eq_one_or_two h)

theorem sporadicSchreierCase_Co1 :
    SporadicSchreierCase .Co1 :=
  sporadicSchreierCase_of_card_eq_one_or_two (Or.inl card_outer_Co1)

theorem sporadicSchreierCase_Co2 :
    SporadicSchreierCase .Co2 :=
  sporadicSchreierCase_of_card_eq_one_or_two (Or.inl card_outer_Co2)

theorem sporadicSchreierCase_HN :
    SporadicSchreierCase .HN :=
  sporadicSchreierCase_of_card_eq_one_or_two (Or.inr card_outer_HN)

theorem sporadicSchreierCase_Ly :
    SporadicSchreierCase .Ly :=
  sporadicSchreierCase_of_card_eq_one_or_two card_outer_Ly

theorem sporadicSchreierCase_Th :
    SporadicSchreierCase .Th :=
  sporadicSchreierCase_of_card_eq_one_or_two (Or.inl card_outer_Th)

theorem sporadicSchreierCase_B :
    SporadicSchreierCase .B :=
  sporadicSchreierCase_of_card_eq_one_or_two (Or.inl card_outer_B)

theorem sporadicSchreierCase_J4 :
    SporadicSchreierCase .J4 :=
  fun _ _ _ _ _ he => CFSG.Sporadic.J4Schreier.R3E_J4_catalog_Schreier he

theorem sporadicSchreierCase_M :
    SporadicSchreierCase .M :=
  fun _ _ _ _ _ ⟨e⟩ => isSolvable_outer_of_simple_M e

theorem schreierFor_catalog :
    CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog :=
  catalogSchreier_of_remaining sporadicSchreierCase_J4
    sporadicSchreierCase_Co1 sporadicSchreierCase_Co2 sporadicSchreierCase_Fi22
    sporadicSchreierCase_Fi23 sporadicSchreierCase_Fi24 sporadicSchreierCase_McL
    sporadicSchreierCase_He sporadicSchreierCase_Suz sporadicSchreierCase_HN
    sporadicSchreierCase_Ly sporadicSchreierCase_Th sporadicSchreierCase_B
    sporadicSchreierCase_M

end CFSG.RankThree.PartOne.SPOR
