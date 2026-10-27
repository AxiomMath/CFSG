module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallNarrow
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

import CFSG.LocalAnalysis.UniquenessCase.UC22ListB
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512L3SD
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54ChevOdd
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallG2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallL3Wr
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SylowOver
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54OddDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem asch54Case_oddLie_small_of_psp4 (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hSp : K_Asch511SylowOvergroupsPSp4) :
    Asch54Case fun X _ => ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ Asch511SmallLie X r := by
  intro Q _ _ L T hKQ hLn hLs hLnab hC hPL hL0 hT hnu
  obtain ⟨r, hr, hr2, hG | hPSp | hL3 | hU3⟩ := hPL
  · exact asch54Case_g2Prime hS Q L T hKQ hLn hLs hLnab hC ⟨r, hr, hr2, hG⟩ hL0 hT hnu
  · exact asch54Case_of_sylowOvergroups
      (P := fun X _ => ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ CFSG.Blueprint.LieModel X .PSp 2 r 1) hS
      (fun X _ hX => CFSG.LocalAnalysis.UniquenessCase.UC22.uc22lb_listB_facts
        CFSG.LocalAnalysis.UniquenessCase.UC22.listBExceptionalFacts
        ((isCalL0_iff_asc1930ListB X).1 hX))
      (fun X _ _ ⟨r, hr, hr2, h⟩ => hSp X r hr hr2 h)
      Q L T hKQ hLn hLs hLnab hC ⟨r, hr, hr2, hPSp⟩ hL0 hT hnu
  all_goals
    have h4 : r % 4 = 1 ∨ r % 4 = 3 := by
      have := Nat.odd_iff.mp (hr.odd_of_ne_two hr2)
      omega
  · rcases h4 with h4 | h4
    · exact asch54Case_l3EpsWr hS Q L T hKQ hLn hLs hLnab hC ⟨r, hr, hr2, Or.inl ⟨h4, hL3⟩⟩
        hL0 hT hnu
    · exact asch54Case_of_sectionalTwoRankLE
        (P := fun X _ => CFSG.Blueprint.LieModel X .PSL 3 r 1) hS
        (fun _ _ _ h => sectionalTwoRankLE_two_of_lieModel_psl_three hr hr2 h (by rwa [pow_one]))
        Q L T hKQ hLn hLs hLnab hC hL3 hL0 hT hnu
  · rcases h4 with h4 | h4
    · exact asch54Case_of_sectionalTwoRankLE
        (P := fun X _ => CFSG.Blueprint.LieModel X .PSU 3 r 1) hS
        (fun _ _ _ h => sectionalTwoRankLE_two_of_lieModel_psu_three hr hr2 h (by rwa [pow_one]))
        Q L T hKQ hLn hLs hLnab hC hU3 hL0 hT hnu
    · exact asch54Case_l3EpsWr hS Q L T hKQ hLn hLs hLnab hC ⟨r, hr, hr2, Or.inr ⟨h4, hU3⟩⟩
        hL0 hT hnu

end CFSG.LocalAnalysis.WeakClosure81

end
