module

public import CFSG.LocalAnalysis.WeakClosure81.W18Pack

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
  Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem packSpace_le_fixSub (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (A : Subgroup (LGL 2 M.W)) : x.packSpace M A ≤ fixSub A := by
  refine iSup_le fun ⟨g, _, hA⟩ => ?_
  subst hA
  have hle : vInH V H g ≤ H := inf_le_right
  show M.sp (conjSubgroup V₀ g) ≤ fixSub (M.img (vInH V H g))
  rw [M.fixSub_img hle]
  refine M.sp_mono fun v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hab := E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g
  have hv' : v ∈ conjSubgroup V g :=
    mem_conjSubgroup_iff.2 (x.hyp.setting.pair.le (mem_conjSubgroup_iff.1 hv))
  have hc := hab.1.is_comm.comm (⟨d, hd.1⟩ : conjSubgroup V g) ⟨v, hv'⟩
  exact congrArg Subtype.val hc

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
