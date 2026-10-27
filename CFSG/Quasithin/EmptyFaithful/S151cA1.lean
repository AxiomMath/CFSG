module

public import CFSG.Quasithin.EmptyFaithful.S151cStmt2
public import CFSG.Quasithin.EmptyFaithful.S15112
public import CFSG.Quasithin.EmptyFaithful.S15114
public import CFSG.Quasithin.EmptyFaithful.S151b110
public import CFSG.Quasithin.EmptyFaithful.S151b111

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem stageLemma1519_of_ce (h14 : StageLemma1414) (h17 : StageLemma1417)
    (h317 : Theorem317Statement) (h15 : StageLemma1515CE) (h16 : StageLemma1516CE) :
    StageLemma1519 := by
  intro G _ _ T Mc M h hM hCE
  exact lemma_15_1_9 h14 h17 h317 h hM hCE (h15 G T Mc M h hM hCE) (h16 G T Mc M h hM hCE)

theorem notDualFF1512_of_ce (h1416 : StageLemma1416) (h1515 : StageLemma1515CE)
    (h158 : StageLemma1518) (h159 : StageLemma1519) : NotDualFF1512 := by
  intro G _ _ T Mc M h hM hCE
  have hred : IsTwoReducedIn M (V154 T Mc M) := (h1515 G T Mc M h hM hCE).reduced
  have hsix : autOn (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) (V154 T Mc M) =
      autOn M (V154 T Mc M) := (h159 G T Mc M h hM hCE).six_autOn
  have hsolv : Group.IsSolvable ↥(autOn M (V154 T Mc M)) :=
    isSolvable_autOn_of_perfectCore_le hred.2.1 ((h1416 G T Mc h).1 M _ hM.1.1 hred)
  rintro ⟨hV, hd⟩
  refine not_isDualFFInt_of_one_lt_qInt hV (by rw [hsix]; exact hsolv)
    (by rw [hsix]; exact autOn_pCore_trivial hred) ?_ hd
  have hq2 : qInt M (V154 T Mc M) hV = 2 := by
    rw [← qOn_eq hV]
    exact qOn_eq_two_of_lemma1518 (h158 G T Mc M h hM hCE)
  rw [qInt_congr hV hsix, hq2]
  norm_num

theorem stageLemma15110_of_ce (h1416 : StageLemma1416) (h1515 : StageLemma1515CE) :
    StageLemma15110 := by
  intro G _ _ T Mc M h hM hCE c6
  have hred := (h1515 G T Mc M h hM hCE).reduced
  exact lemma15110_of151b h hM hred
    (isSolvable_autOn_of_perfectCore_le hred.2.1 ((h1416 G T Mc h).1 M _ hM.1.1 hred)) c6

theorem stageLemma15113Three_of_ce (h157 : StageLemma1517) (h158 : StageLemma1518)
    (h159 : StageLemma1519) (h1515 : StageLemma1515CE) (h15110 : StageLemma15110) :
    StageLemma15113Three := by
  intro G _ _ T Mc M h hM hCE
  have hred := (h1515 G T Mc M h hM hCE).reduced
  exact lemma15113Three_of_cases151b h hM (h157 G T Mc M h hM hCE) (h158 G T Mc M h hM hCE)
    (h159 G T Mc M h hM hCE) hred (h15110 G T Mc M h hM hCE)
    (fun hV => rank_bound_five151b hM hV)

theorem stageLemma15113Four_of_ce (h157 : StageLemma1517) (h158 : StageLemma1518)
    (h159 : StageLemma1519) (h1515 : StageLemma1515CE) (h15110 : StageLemma15110)
    (h1512four : StageLemma15112Four) : StageLemma15113Four := by
  intro G _ _ T Mc M h hM hCE
  have hred := (h1515 G T Mc M h hM hCE).reduced
  have hone := lemma_15_1_13_one h hM (fun H hH => h1512four G T Mc M h hM hCE H hH)
  have h2 := lemma_15_1_13_two h hM (h157 G T Mc M h hM hCE) (h159 G T Mc M h hM hCE) hone
  exact lemma15113Four_of_cases151b h hM (h157 G T Mc M h hM hCE) (h158 G T Mc M h hM hCE)
    (h159 G T Mc M h hM hCE) hred (h15110 G T Mc M h hM hCE)
    (fun hV => rank_bound_five151b hM hV) h2

theorem stageLemma15112_of_ce (h319 : Lemma319Statement) (h1416 : StageLemma1416)
    (h1515 : StageLemma1515CE) (h158 : StageLemma1518) (h159 : StageLemma1519)
    (h16 : StageLemma1516CE) (h1511 : StageLemma15111) (h4 : StageLemma15112Four) :
    StageLemma15112 := by
  intro G _ _ T Mc M h hM hCE H hH
  exact ⟨lemma_15_1_12_concl319 h319 h hM (h158 G T Mc M h hM hCE) (h159 G T Mc M h hM hCE)
    (h16 G T Mc M h hM hCE) (notDualFF1512_of_ce h1416 h1515 h158 h159 G T Mc M h hM hCE) hH
    (h1511 G T Mc M h hM hCE H hH).1, h4 G T Mc M h hM hCE H hH⟩

theorem stageLemma15114_of_ce (hStep : Step1514Gen) (h157 : StageLemma1517)
    (h15 : StageLemma1515CE) (h159 : StageLemma1519) (h16 : StageLemma1516CE)
    (h1512 : StageLemma15112) : StageLemma15114 := by
  intro G _ _ T Mc M h hM hCE
  exact lemma_15_1_14 hStep h hM hCE (h157 G T Mc M h hM hCE) (h15 G T Mc M h hM hCE)
    (h159 G T Mc M h hM hCE) (h16 G T Mc M h hM hCE)
    (fun H hH => (h1512 G T Mc M h hM hCE H hH).2)

theorem stage151_of_inputs_ce (h316 : Theorem316Statement) (h317 : Theorem317Statement)
    (h319 : Lemma319Statement) (h1414 : StageLemma1414) (h1416 : StageLemma1416)
    (h1417 : StageLemma1417) (hD : Description1512CE) (hN : Nilpotency1512CE)
    (hStep : Step1514Gen) (h157 : StageLemma1517) (h158 : StageLemma1518)
    (h1511one : StageLemma15111One) (h1512four : StageLemma15112Four) :
    StageLemma1511 ∧ StageLemma1515CE ∧ StageLemma1516CE ∧ StageLemma1519 ∧ StageLemma15112 ∧
      StageLemma15113 ∧ StageLemma15114 := by
  have h15 : StageLemma1515CE := stageLemma1515CE_of_description hD
  have h16 : StageLemma1516CE := stageLemma1516CE_of hN
  have h159 : StageLemma1519 := stageLemma1519_of_ce h1414 h1417 h317 h15 h16
  have h15110 : StageLemma15110 := stageLemma15110_of_ce h1416 h15
  have h15111 : StageLemma15111 := stageLemma15111_of_one h158 h159 h1511one
  have h1512 : StageLemma15112 :=
    stageLemma15112_of_ce h319 h1416 h15 h158 h159 h16 h15111 h1512four
  have h3 : StageLemma15113Three := stageLemma15113Three_of_ce h157 h158 h159 h15 h15110
  have h4 : StageLemma15113Four := stageLemma15113Four_of_ce h157 h158 h159 h15 h15110 h1512four
  exact ⟨stageLemma1511_of_theorem316 h316, h15, h16, h159, h1512,
    stageLemma15113_of h157 h159 h1512 h3 h4, stageLemma15114_of_ce hStep h157 h15 h159 h16 h1512⟩

end CFSG.Quasithin
