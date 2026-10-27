module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.BSevenGen
public import CFSG.RankThree.PartOne.CTP.FusionSound

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.RankThree.PartOne.CTP.Fus CFSG.HardMathSupport.Dickson.I271.BSevenGen

theorem fusionGenerationOf_B_seven_of_gen :
    FusionGenerationOf NativeSporadic.B 7 := by
  obtain ⟨he, he1, hf, hef, hfe, htop⟩ := bSevenGen_facts
  have hf1 : sTwo ^ 10 ≠ 1 := by simpa using hfe 0 (by norm_num)
  have hmemE : sOne ^ 10 ∈ Subgroup.closure ({sOne ^ 10, sTwo ^ 10} : Set NativeSporadic.B) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hmemF : sTwo ^ 10 ∈ Subgroup.closure ({sOne ^ 10, sTwo ^ 10} : Set NativeSporadic.B) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨Subgroup.closure {sOne ^ 10, sTwo ^ 10}, {sOne, sTwo},
    isPGroup_closure_pair Nat.prime_seven he hf hef, ?_, htop, ?_⟩
  · intro hb
    rw [hb] at hmemE
    exact he1 (Subgroup.mem_bot.1 hmemE)
  · rintro g (rfl | rfl)
    · refine ⟨sOne ^ 10, hmemE, he1, ?_⟩
      rw [(Commute.self_pow sOne 10).eq, mul_inv_cancel_right]
      exact hmemE
    · refine ⟨sTwo ^ 10, hmemF, hf1, ?_⟩
      rw [(Commute.self_pow sTwo 10).eq, mul_inv_cancel_right]
      exact hmemF

end CFSG.Sporadic.Bridge.B
