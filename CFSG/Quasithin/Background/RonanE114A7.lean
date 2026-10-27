module

public import CFSG.Quasithin.H13.A7NParam
public import CFSG.Quasithin.Vol2.Ch11SecE3LieMain

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11

variable {G : Type} [Group G] [Finite G]

theorem not_odd_of_two_dvd_card {H : Subgroup G} (h : 2 ∣ Nat.card H) : ¬ Odd (Nat.card G) := by
  intro hodd
  have h1 := Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card H)
  exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h)

theorem nParam_eq_one_of_isAlt7
    (hA7 : IsAlt 7 (ASInputs.FStar G)) : E1.nParam (⊤ : Subgroup G) = 1 := by
  refine le_antisymm (H13.A7NP.nParam_le_one_of_fStar_alt7 hA7) ?_
  obtain ⟨e⟩ := hA7
  refine SecE3.one_le_nParam_of_not_odd (not_odd_of_two_dvd_card (H := CFSG.generalizedFitting G) ?_)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

end CFSG.Quasithin.RonanE114
