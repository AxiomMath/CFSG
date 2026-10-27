module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# Quasisimplicity of perfect central extensions

A perfect group surjecting onto a simple group through a central kernel is
quasisimple.  This is the final abstract lift needed after identifying the
simple quotient image of a component normal closure in a `D`-group.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A nontrivial perfect central extension of a simple group is quasisimple. -/
public theorem isQuasisimple_of_perfect_of_ker_le_center_of_surjective_simple
    {N S : Type u} [Group N] [Group S]
    (f : N →* S) (hf : Function.Surjective f)
    (hNne : Nontrivial N) (hNperf : Group.IsPerfect N)
    (hSsimple : IsSimpleGroup S)
    (hker : f.ker ≤ Subgroup.center N) :
    IsQuasisimple N := by
  let : Nontrivial N := hNne
  let : Group.IsPerfect N := hNperf
  let : IsSimpleGroup S := hSsimple
  have hSperf : Group.IsPerfect S :=
    Group.IsPerfect.ofSurjective hf
  let : Group.IsPerfect S := hSperf
  have hScenter : Subgroup.center S = ⊥ := by
    rcases (hSsimple.eq_bot_or_eq_top_of_normal (Subgroup.center S)) with hbot | htop
    · exact hbot
    · exfalso
      have hcomm : IsMulCommutative S :=
        Subgroup.center_eq_top_iff.mp htop
      exact Group.IsPerfect.not_isMulCommutative S hcomm
  have hcenter_ker : Subgroup.center N ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hfz : f z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hf y
      simpa using congrArg f (Subgroup.mem_center_iff.mp hz x)
    have hfzbot : f z ∈ (⊥ : Subgroup S) := by
      simpa [hScenter] using hfz
    exact Subgroup.mem_bot.mp hfzbot
  have hker_eq : f.ker = Subgroup.center N :=
    le_antisymm hker hcenter_ker
  let eRangeTop : f.range ≃* (⊤ : Subgroup S) :=
    MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hf)
  let eQuot : N ⧸ f.ker ≃* S :=
    ((QuotientGroup.quotientKerEquivRange f).trans eRangeTop).trans
      Subgroup.topEquiv
  let eCenterKer : N ⧸ Subgroup.center N ≃* N ⧸ f.ker :=
    QuotientGroup.quotientMulEquivOfEq
      (M := Subgroup.center N) (N := f.ker) hker_eq.symm
  have hquotSimple : IsSimpleGroup (N ⧸ Subgroup.center N) :=
    (MulEquiv.isSimpleGroup_congr (eCenterKer.trans eQuot)).mpr hSsimple
  exact ⟨hNne, (Group.isPerfect_def).1 hNperf, hquotSimple⟩

end CFSG.GorensteinWalter
