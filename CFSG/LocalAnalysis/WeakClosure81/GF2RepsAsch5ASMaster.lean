module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASSec
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Sec
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASEF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

theorem inFSqAS_of_cfShape {Q : Type} [Group Q] [Finite Q] {H T M : Subgroup Q} {j : ℕ}
    (hj : 1 ≤ j) (hT : IsSylowIn 2 T H) (hU : calNIn H T = {M})
    {P : ∀ (X : Type) [Group X], Prop} (hCF : CFShape ↥H P) (hS : ShapeInEAS j P) :
    InFSqAS j H := by
  have hCFb : CFShape (Bar2 H) P := cfShape_quotient (CFSG.pCore 2 ↥H) hCF
  have hTb : IsSylowIn 2 (barImage H T) ⊤ := isSylowIn_barImage hT
  have hE : E1.InE j (⊤ : Subgroup (Bar2 H)) := inE_of_cfShape hj hTb hCFb hS
  exact inFAS_top_of_inE j hE
    ⟨barImage H T, isSylowOf_two_iff_isSylowIn.mpr hTb, hasUniqueMaxOver_barImage hT hU⟩
    (pCore_two_bar2_eq_bot H)

theorem inFSqAS_of_isSolvable {Q : Type} [Group Q] [Finite Q] {H T M : Subgroup Q}
    (hT : IsSylowIn 2 T H) (hU : calNIn H T = {M}) (hH : Group.IsSolvable ↥H) :
    InFSqAS 1 H := by
  haveI := hH
  exact inFSqAS_of_cfShape le_rfl hT hU (P := fun _ _ => False) (cfShape_of_isSolvable _)
    (fun _ _ _ _ _ hP => hP.elim)

end CFSG.LocalAnalysis.WeakClosure81

end
