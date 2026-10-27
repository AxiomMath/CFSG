module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SFrontier
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKTwo
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKCentL3
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKCentJ2

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138SylowSN

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13.Ronan138S

theorem item138SylowN_of_item138N (h : Item138N) : Item138SylowN := by
  intro G _ _ A c L E hH F hF _
  obtain ⟨hD, hL3, hcE, hE3, hE27, hEN, hEC, hST, hC⟩ := hH
  obtain ⟨⟨hFEL, hF3, hF27, hFfus, hFN⟩, hFL⟩ := hF
  exact ((h G A c L hD hL3 E hcE hE3 hE27 hEN hEC hST hC).2.2 F hFEL hF3 hF27 hFL hFfus hFN).1

section Certs


theorem item138SylowN_holds
    : Item138SylowN :=
  item138SylowN_of_item138N Ronan138S.item138N_holds

theorem item138SN_holds
    : Item138SN := by
  have hcore : Step13PZeroCore := Ronan138P5.step13PZeroCore_of_cover
    Sec4.Ronan148R.k419UnitaryCensusCover_holds Sec11.Close.closed_sec4Item4_6
    Sec11.Close.closed_sec4Item4_8 Sec4.Ronan148L.kf138TrialityPGUCent
  have hSeven : Step138ENeDSeven :=
    step138ENeDSeven_of (step138ENeDSevenT_of rank3II_13_1_holds sporadicModels131
      (step138ENeDHeisT_of rank3II_13_1_holds sporadicModels131))
  have hTwo : Step138ENeDTwo := step138ENeDTwo_of Ronan138W.omegaCent_holds hcore
  have h45 : Sec4.Item4_5 := Sec11.Close.closed_sec4Item4_5
  have h48 : Sec4.Item4_8 := Sec11.Close.closed_sec4Item4_8
  have h422 : Sec4.Item4_22 :=
    KFacts.rank3II_4_22_of_items_noItem41 h45 Sec11.Close.closed_tBLitGriessMultipliersAllModels
      Sec11.Close.closed_sec4Item4_3
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have h131 : Item131 := rank3II_13_1_holds
  have h133 : Item133 := rank3II_13_3_of h131 h422 h45
  have hsetAt : Item13SetupAt := item13SetupAt_of h422 h45
  have hENeD : Step138ENeD := step138ENeD_of h131 sporadicModels131 hsetAt hTwo hSeven
  have hNC : Step138NoCompF :=
    step138NoCompF_of_cent sporadicModels131 h48 hsetAt h133 hENeD
      (step138CentPGL_of h131 sporadicModels131) (step138CentL3_of h48)
      (step138CentJ2_of sporadicModels131 h415 h48)
  have hKS : Step138KStr :=
    step138KStr_of sporadicModels131 h415 h48 hsetAt h133 hENeD hNC kf138TypeTwo
  exact item138SN_of h131 sporadicModels131 Sec4.Sporadic.rank3II_4_14_local KFacts.ks18M12
    (fun X _ hX => Toolkit.m12ThreeLocalData X hX) hKS

end Certs

end CFSG.RankThree.PartTwo.Sec13.Ronan138SylowSN
