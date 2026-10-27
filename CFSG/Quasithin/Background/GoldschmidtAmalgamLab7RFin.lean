module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7RClose
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7RCamp
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8SymInput

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
  CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3 CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem not_normal_B_of_twoSys (h : TwoSys A B z V c V₂) (h3 : GoldHyp3 A B z V)
    (hb : 5 ≤ critDist (A ⊔ B) A B V) :
    ¬ B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
  intro hN
  obtain ⟨y, hyB, hy3⟩ := exists_orderOf_eq_three h.gold
  exact false_of_comm_mem h h3 hb hyB hy3 (comm_mem_of_campbell h hN hyB hy3)

theorem notNormalBTwoSys (D : Type*) [Group D] [Finite D] : GoldAmLab8.NotNormalBTwoSys D :=
  fun _ _ _ _ _ _ h h3 hb => not_normal_B_of_twoSys h h3 hb

end GoldAmLab7

namespace GoldAmL3

theorem b5LeNoACInput : B5LeNoACInput.{u} :=
  b5LeNoACInput_of_notNormalBTwoSys fun D _ _ => GoldAmLab7.notNormalBTwoSys D

end GoldAmL3

end F6

end CFSG.Quasithin
