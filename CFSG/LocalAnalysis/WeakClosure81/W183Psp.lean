module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASBasic
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5LiftB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem false_of_psp4_three (hPS : Asch5_PSp4Three) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (c : MinCex183 D V₀ V H i) (hK : OInf H = kerMV V H) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G) (fun X _ => LieModel X .PSp 2 3 1)) : False := by
  rw [← hK] at hL hX
  exact false_of_psp4Three hPS c.hyp.isSylowIn_T (c.calNIn_eq_AS h5_11 h5_13) hL hLT hX

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
