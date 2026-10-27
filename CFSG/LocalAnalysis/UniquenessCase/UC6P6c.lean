module

public import CFSG.LocalAnalysis.UniquenessCase.UC6P6a
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

section C621List


namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem c621_of_list_of_ne_three (hr : m.r ≠ 3) (h620 : m.C620) (hL : m.L620)
    (hOL : CFSG.pPrimeCore m.r ↥m.L = ⊥) : m.C621 := by
  have e := m.equivLbar hOL
  rcases hL.2 with hL2 | ⟨hr3, -⟩ | ⟨hr5, hT | hA⟩
  · exact m.c621_of_L2 h620 (LieModel.of_mulEquiv e.symm hL2)
  · exact absurd hr3 hr
  · exact m.c621_of_tits h620 hr5 (isoLie_tits_of_lieModel (LieModel.of_mulEquiv e.symm hT))
  · obtain ⟨f⟩ := hA
    obtain ⟨D⟩ := exists_A10Setup m h620 hr5 ⟨e.trans f⟩
    exact D.c621 h620 hr5

theorem c621_of_L620_of_ne_three (hr : m.r ≠ 3) (hMult : UCK.KMultList620)
    (h67 : R6_7 (dataOfSetup4 m.hS m.hU m.S)) (h619 : m.C619)
    (hq : CFSG.Open.IsQuasisimple ↥m.L) (hL : m.L620) : m.C621 := by
  have hr3 : 3 < m.r := by
    have := m.hr.two_le
    have := m.d.odd
    omega
  have hcen : center ↥m.L = ⊥ :=
    m.center_L_eq_bot h67 h619 (m.hmult_of_kMultList620 hMult hL hq hr3)
  have hOL : CFSG.pPrimeCore m.r ↥m.L = ⊥ :=
    le_bot_iff.1 (hcen ▸ m.pPrimeCore_le_center_uc6 hq (m.r_dvd_card_L hL.1))
  exact m.c621_of_list_of_ne_three hr hL.1 hL hOL

end Mz614

end C621List

end CFSG.LocalAnalysis.UniquenessCase.UC6
