module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.Background.B3Sec

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

theorem autI_baum_le [Finite G] {V R : Subgroup G} (hV : IsElemAbelian 2 V) (hVR : V ≤ R)
    (hRN : R ≤ normalizer (V : Set G)) :
    autI hV (baum R) ≤ autI hV R ⊓ centSub (fixV (autI hV (thompsonJ R))) := by
  have hJN : thompsonJ R ≤ normalizer (V : Set G) := (thompsonJ_le_self R).trans hRN
  refine le_inf (autI_mono hV (B2F.baum_le R)) ?_
  intro φ hφ
  obtain ⟨x, hx, rfl⟩ := (mem_autI hV).1 hφ
  rw [mem_centSub]
  intro u hu
  have hu2 := (mem_fixV_autI hV hJN u).1 hu
  have hE : u.val ∈ omegaOneCenterOf (thompsonJ R) :=
    inf_centralizer_thompsonJ_le hV hVR ⟨u.val_mem, hu2⟩
  have hcomm : (x : G) * u.val = u.val * x :=
    (Subgroup.mem_centralizer_iff.1 hx.2 u.val hE).symm
  refine IntMod.val_injective ?_
  rw [convI_apply_val, hcomm, mul_inv_cancel_right]

end CFSG.Quasithin.H13.U3.GC137
