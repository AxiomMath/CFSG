module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.RankOne

namespace CFSG
end CFSG
open CFSG

/-!
# The simple rank-two exclusion

The final clause of Theorem SE uses `[IG; 15.2, 15.3]` to exclude the
rank-one alternative for a simple group with a strongly embedded subgroup.
The rank-one factorization is proved in `SE.RankOne`; here we supply the
checked simple-group bridge and expose the exact interface consumed by the
final reduction.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

/-- A finite simple group with a strongly embedded subgroup has `2`-rank at
least two.  This is the `[IG; 15.2, 15.3]` exclusion used in the final clause
of Theorem SE. -/
public theorem simpleStronglyEmbeddedRankTwo :
    SimpleStronglyEmbeddedRankTwo.{u} := by
  intro X _ _ M hX hM
  have hcore : involutionCore X = ⊤ :=
    hM.involutionCore_eq_top_of_isSimple hX
  have hnsolv : ¬ Group.IsSolvable X := by
    intro hsolv
    let : IsSimpleGroup X := hX
    have hcomm : ∀ a b : X, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
    let : CommGroup X :=
      { (inferInstance : Group X) with
        mul_comm := hcomm }
    have hMnormal : M.Normal := Subgroup.normal_of_isMulCommutative M
    rcases (haveI := hMnormal; hX.eq_bot_or_eq_top_of_normal M) with hMbot | hMtop
    · obtain ⟨x, hxM, hx⟩ := hM.exists_involution
      exact hx.ne_one (Subgroup.mem_bot.mp (hMbot ▸ hxM))
    · exact hM.ne_top hMtop
  have hMrank : TwoRankAtLeastTwo M :=
    hM.twoRankAtLeastTwo_of_not_solvable_of_involutionCore_eq_top
      hcore hnsolv
  exact hMrank.map_of_injective M.subtype Subtype.val_injective

end CFSG.BenderSuzuki
