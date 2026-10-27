module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22FCode3
public import CFSG.Quasithin.Background.HFCode22

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.M22F

theorem code22Ord3Rank6_m22f_proved :
    CFSG.Quasithin.H13.M22F.Code22Ord3Rank6_m22f := by
  intro g hg
  have hLM : CFSG.Quasithin.H.Mathieu.IsOver (rhoC10 mog22 mog22_le_mog22plus).range
      (rhoC10 mog22plus le_rfl).range := by
    refine ⟨?_, le_of_eq normalizer_rhoC10_mog22.symm⟩
    rw [range_rhoC10_mog22]
    exact Subgroup.map_le_range _ _
  have hz : orderOf (rhoC10 mog22plus le_rfl g) = 3 :=
    (orderOf_injective _ rhoC10_mog22plus_injective g).trans hg
  exact code22_odd_le (z := rhoC10 mog22plus le_rfl g) hLM
    CFSG.Quasithin.B45Mat.M22.code22_rhoC10 ⟨g, rfl⟩ Nat.prime_three (by norm_num) hz

end CFSG.Quasithin.H13.Mat
