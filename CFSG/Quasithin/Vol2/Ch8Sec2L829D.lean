module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829C
public import CFSG.Quasithin.Vol2.Ch8Sec2D2Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs

theorem stmt8_2_9_12_of (hmod : StmtFSUModule)
    (h825 : Stmt8_2_5) (hE214 : AS_E_2_14) (hthree : Stmt8_2_9_three)
    (hcoc : Step829Cocode) (hL3M22 : Step829L3M22) : Stmt8_2_9_12 := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hhH hC
  obtain ⟨hw, -, hn1, hT9, hT22, hT24, hT24c, -⟩ :=
    h825 G T L I hyp h731 h821 hc hrow H h k hH hhH hC
  have hk2 : k ≤ 2 := by
    have hwk : wParam T (fsuV T I) ≤ 2 := by
      rcases id hrow with ⟨n, hr⟩ | hr | hr | hr
      · rw [(hT9 ⟨n, hr⟩).1]
        norm_num
      · rw [(hT22 hr).1]
        norm_num
      · rw [(hT24 hr).1]
        norm_num
      · rw [(hT24c hr).1]
    rw [hw] at hwk
    exact_mod_cast hwk
  have hTO : T ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) := by
    rcases id hrow with ⟨n, hr⟩ | hr | hr | hr
    · have hn := hn1 n hr
      subst hn
      exact hL3M22 G T L I hyp h731 h821 hc hrow H h k hH hhH hC (Or.inl hr)
    · exact hL3M22 G T L I hyp h731 h821 hc hrow H h k hH hhH hC (Or.inr hr)
    · exact absurd hr (hthree G T L I hyp h731 h821 hc hrow)
    · exact hcoc G T L I hyp h731 h821 hc hrow H h k hH hhH hC hr
  exact concl829_of_82 hE214 hmod hyp hH hC hk2 hTO

end CFSG.Quasithin.H13
