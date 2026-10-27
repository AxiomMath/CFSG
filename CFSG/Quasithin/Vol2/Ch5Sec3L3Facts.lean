module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3
public import CFSG.Quasithin.Vol2.Ch5Sec3L3Semi

public section

namespace CFSG.Quasithin.H13

theorem stmt5_3_L3_facts_of (h527 : Stmt5_2_7) (h531 : Stmt5_3_1) : Stmt5_3_L3_facts := by
  intro G _ _ T M L V H B D L₂ n f hyp hty hf
  exact ⟨Sec53L3.l3facts_one h527 h531 hyp hty hf, Sec53L3.l3facts_two h527 hyp hty hf,
    Sec53L3.l3facts_three h527 hyp hty hf, Sec53L3.l3facts_four h527 hyp hty hf,
    Sec53L3.l3facts_five h527 h531 hyp hty hf,
    fun hf3 => Sec53L3.l3facts_six_of_three_le h527 h531 hyp hty hf hf3⟩

end CFSG.Quasithin.H13
