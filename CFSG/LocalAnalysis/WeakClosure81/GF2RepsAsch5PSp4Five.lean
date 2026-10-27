module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5LiftB
public import CFSG.LocalAnalysis.WeakClosure81.PSpFourFiveOvergroups

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (OInf)
open CFSG.Blueprint (LieModel)

theorem false_of_psp4Five {Q : Type} [Group Q] [Finite Q]
    {H T M L : Subgroup Q} (hT : IsSylowIn 2 T H) (hU : calNIn H T = {M})
    (hL : IsComponentModN (OInf H) H L) (hLT : L ⊔ T = H)
    (hX : HasQuotShape L (OInf H : Set Q) (fun X _ => LieModel X .PSp 2 5 1)) : False := by
  exact false_of_psp4_overgroups (p := 5)
    (fun X _ _ hX => exists_overgroups_of_psp4_five X hX) hT hU hL hLT hX

end CFSG.LocalAnalysis.WeakClosure81
