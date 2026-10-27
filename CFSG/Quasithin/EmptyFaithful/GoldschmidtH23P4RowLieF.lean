module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutLie
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.H23P4

section U33


theorem rowOK_of_isPSU33 {X : Type} [Group X] [Finite X] (h : IsPSU 3 3 1 X) : RowOK X where
  center := CFSG.Quasithin.SBc11.center_eq_bot_of_list (Or.inr (Or.inr h))
  out := CFSG.Quasithin.H23Out.out5Pow_of_isPSU33 h
  idx := NoFiveIndex.of_not_dvd_card (by
    rw [CFSG.Quasithin.SBc11.card_of_isPSU_three_three h]
    norm_num)

end U33

section D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld


theorem center_eq_bot_of_is3D4 {X : Type} [Group X] (h : Is3D4 2 1 X) :
    Subgroup.center X = ⊥ := by
  have hm0 : ChevalleyExceptionalModel X .trialityD4 2 1 := h
  obtain ⟨hp, hf, -⟩ := hm0.1
  have hm' : TwistedChevalleyModel X .D4 (2 ^ 1) := hm0.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm'
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := 1) hf K hK σ hσ
  rw [← Subgroup.map_center_eq e.symm, hZ, Subgroup.map_bot]

theorem not_five_dvd_card_is3D4 {X : Type} [Group X] (h : Is3D4 2 1 X) : ¬ 5 ∣ Nat.card X := by
  have hm0 : ChevalleyExceptionalModel X .trialityD4 2 1 := h
  have hc := card_chevalleyExceptionalModel_two hm0
  simp only at hc
  rw [hc]
  unfold CFSG.Open.ordTrialityD4
  norm_num

theorem rowOK_of_is3D4 {X : Type} [Group X] [Finite X] (h : Is3D4 2 1 X) : RowOK X where
  center := center_eq_bot_of_is3D4 h
  out := CFSG.Quasithin.H23Out.out5Pow_of_is3D4 h
  idx := NoFiveIndex.of_not_dvd_card (not_five_dvd_card_is3D4 h)

end D4

end CFSG.Quasithin.H23P4
