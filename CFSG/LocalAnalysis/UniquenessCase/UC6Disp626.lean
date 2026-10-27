module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C626L2Gen
public import CFSG.LocalAnalysis.UniquenessCase.UC6C626Three
public import CFSG.LocalAnalysis.UniquenessCase.UC6M11C626
public import CFSG.LocalAnalysis.UniquenessCase.UC6L34C626
public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsC626

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)

section Disp626


namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem pPrimeCore_eq_bot_of_ne_three (hr : m.r ≠ 3) (hMult : UCK.KMultList620)
    (h67 : R6_7 (dataOfSetup4 m.hS m.hU m.S)) (h619 : m.C619) (hq : CFSG.Open.IsQuasisimple ↥m.L)
    (hL : m.L620) : CFSG.pPrimeCore m.r ↥m.L = ⊥ := by
  have hr3 : 3 < m.r := by
    have := m.hr.two_le
    have := m.d.odd
    omega
  have hcen : center ↥m.L = ⊥ :=
    m.center_L_eq_bot h67 h619 (m.hmult_of_kMultList620 hMult hL hq hr3)
  exact le_bot_iff.1 (hcen ▸ m.pPrimeCore_le_center_uc6 hq (m.r_dvd_card_L hL.1))

theorem c626gen_of_L620 (hMult : UCK.KMultList620) (h67 : R6_7 (dataOfSetup4 m.hS m.hU m.S))
    (h619 : m.C619) (hq : m.r ≠ 3 → CFSG.Open.IsQuasisimple ↥m.L) (hL : m.L620)
    (hres : m.r = 3 → LieModel m.Lbar .PSL 3 2 2 → ¬ m.E ≤ m.L → m.C626gen) : m.C626gen := by
  have h620 := hL.1
  rcases hL.2 with hL2 | ⟨hr3, hM | hL34⟩ | ⟨hr5, hT | hA⟩
  · by_cases hr3 : m.r = 3
    · exact m.c626gen_of_lieModel_three h619 h620 hr3 hL2
    · have hOL := m.pPrimeCore_eq_bot_of_ne_three hr3 hMult h67 h619 (hq hr3) hL
      exact m.c626gen_of_lieModel h620 (LieModel.of_mulEquiv (m.equivLbar hOL).symm hL2)
  · exact m.c626gen_of_m11 h619 h620 hr3 hM
  · by_cases hEL : m.E ≤ m.L
    · exact m.c626gen_of_l34 h619 h620 hr3 hL34 hEL
    · exact hres hr3 hL34 hEL
  · have hOL := m.pPrimeCore_eq_bot_of_ne_three (by omega) hMult h67 h619 (hq (by omega)) hL
    exact c626gen_of_tits m hL hOL hr5 hT
  · have hOL := m.pPrimeCore_eq_bot_of_ne_three (by omega) hMult h67 h619 (hq (by omega)) hL
    exact c626gen_of_A10 m hL hOL hr5 hA

end Mz614

end Disp626

end CFSG.LocalAnalysis.UniquenessCase.UC6
