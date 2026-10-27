module

public import CFSG.Quasithin.H13.A5S136abP
public import CFSG.Quasithin.H13.ZCentLieLinear
public import CFSG.Quasithin.H13.ZCentLieExc
public import CFSG.Quasithin.H13.ZCentLieUnitary
public import CFSG.Quasithin.H13.ZCentLieD4

public section

namespace CFSG.Quasithin.H13.ZCentLie

open CFSG.Quasithin.H13.A5

theorem zCentAt_sylow_of_lieZCentList
    {X : Type} [Group X] [Finite X] (hX : LieZCentList X) (P : Sylow 2 X) :
    ZCentAt (P : Subgroup X) := by
  obtain ⟨f, h | h | h | h | h | h | h⟩ := hX
  · exact zCentAt_sylow_of_psl (Or.inl rfl) (le_trans one_le_two h.1) h.2 P
  · exact zCentAt_sylow_of_psl (Or.inr rfl) (le_trans one_le_two h.1) h.2 P
  · exact zCentAt_sylow_of_psu h.2 P
  · exact zCentAt_sylow_of_g2 (le_trans one_le_two h.1) h.2 P
  · exact zCentAt_sylow_of_trialityD4 (le_trans one_le_two h.1) h.2 P
  · exact zCentAt_sylow_of_ree h.2.2 P
  · exact zCentAt_sylow_of_suzuki h.2.2 P

theorem factLieZCent_holds :
    FactLieZCent := by
  intro X _ _ hX P u w k hu hcu hu1 hw hcw _ hk
  exact zCentAt_sylow_of_lieZCentList hX P u w k hu hcu hu1 hw hcw hk

theorem factLieZCentPGL3_holds : FactLieZCentPGL3 := by
  intro s f hf X _ _ hX P u w k hu hcu hu1 hw hcw _ hk
  cases s
  · exact zCentAt_sylow_of_pgu (le_trans one_le_two hf) hX P u w k hu hcu hu1 hw hcw hk
  · exact zCentAt_sylow_of_pgl3 (le_trans one_le_two hf) hX P u w k hu hcu hu1 hw hcw hk

end CFSG.Quasithin.H13.ZCentLie
