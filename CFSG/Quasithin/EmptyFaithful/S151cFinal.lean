module

public import CFSG.Quasithin.EmptyFaithful.S151cFinalA
public import CFSG.Quasithin.EmptyFaithful.S151cTrans6
public import CFSG.Quasithin.EmptyFaithful.S151cCasei

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Final151c

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem facts_of_refined (h1511 : StageLemma1511) (h1414 : StageLemma1414)
    (h1416 : StageLemma1416) (h1417 : StageLemma1417) (hC : CentralOnComplement1512)
    (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M) :
    DescAt T M (V154 T Mc M) ∧ IsTwoNilpotentOn M (V154 T Mc M) ∧
      Lemma1517ConclAt T M (V154 T Mc M) ∧ Lemma1518ConclAt M (V154 T Mc M) := by
  by_cases hb : Case1512Six T Mc M
  · rw [V154_eq_uJ hb]
    exact facts_of_six h hM hb
  · rw [V154_eq_VZ hb]
    have hVe : IsElemAbelian 2 (VZ T M) := isElemAbelian_VZ h hM.1.1
    have hS := setting151c_of h1511 h1414 h1416 h1417 hC h hM hCE hVe
    have hCE1 : Nat.card (IntMod (VZ T M) hVe) ≠ 4 := hCE.1
    have hCE2 : ¬ IsOFourPlusAct (autI hVe M) := hCE.2
    rcases refined1512 hS hCE1 hCE2 with h6 | hI
    · exact absurd (case1512Six_of_case6Aut h hM hVe h6) hb
    · exact facts_of_caseI h hM.1.1 hVe hI

theorem description1512CE_of (h1511 : StageLemma1511) (h1414 : StageLemma1414)
    (h1416 : StageLemma1416) (h1417 : StageLemma1417) (hC : CentralOnComplement1512) :
    Description1512CE :=
  fun _ _ _ _ _ _ h hM hCE => (facts_of_refined h1511 h1414 h1416 h1417 hC h hM hCE).1

theorem nilpotency1512CE_of (h1511 : StageLemma1511) (h1414 : StageLemma1414)
    (h1416 : StageLemma1416) (h1417 : StageLemma1417) (hC : CentralOnComplement1512) :
    Nilpotency1512CE :=
  fun _ _ _ _ _ _ h hM hCE => (facts_of_refined h1511 h1414 h1416 h1417 hC h hM hCE).2.1

theorem stageLemma1517_of (h1511 : StageLemma1511) (h1414 : StageLemma1414)
    (h1416 : StageLemma1416) (h1417 : StageLemma1417) (hC : CentralOnComplement1512) :
    StageLemma1517 :=
  fun _ _ _ _ _ _ h hM hCE =>
    (lemma1517Concl_iff _ _ _).mpr
      (facts_of_refined h1511 h1414 h1416 h1417 hC h hM hCE).2.2.1

theorem stageLemma1518_of (h1511 : StageLemma1511) (h1414 : StageLemma1414)
    (h1416 : StageLemma1416) (h1417 : StageLemma1417) (hC : CentralOnComplement1512) :
    StageLemma1518 :=
  fun _ _ _ _ _ _ h hM hCE =>
    (lemma1518Concl_iff _ _ _).mpr
      (facts_of_refined h1511 h1414 h1416 h1417 hC h hM hCE).2.2.2

end Final151c

end CFSG.Quasithin
