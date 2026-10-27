module

public import CFSG.Quasithin.Background.E1Amb
public import CFSG.Quasithin.Background.GoldschmidtE23Setup
public import CFSG.Quasithin.Vol2.Ch3zRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace GE23

section Glue

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M V : Subgroup Γ} (hV : IsElemAbelian 2 V)

theorem autI_twoResidual_eq (hHN : H ≤ Subgroup.normalizer (V : Set Γ)) :
    autI hV (twoResidual H) = twoResidual (autI hV H) := by
  rw [← map_star_subgroupOf hV hHN (twoResidual_le H), ← B6.twoResidual_top_eq_subgroupOf,
    B6.twoResidual_map_top (starHom_surjective hV hHN), E1.twoResidual_eq_map_top (autI hV H)]

theorem isRankTwoQuotient_star (hsq : SQTKGroup ↥H) (hHN : H ≤ Subgroup.normalizer (V : Set Γ)) :
    Ch3z.IsRankTwoQuotient ↥(autI hV H) :=
  ⟨↥H, inferInstance, inferInstance,
    fun p hp hp2 => hsq.1 p hp hp2, starHom hV hHN,
    starHom_surjective hV hHN⟩

theorem blkCtx_star (hP4 : AsB15Part4) (hComp : B69.AsB69Component)
    (h : MinParabolic H T M) (hsq : SQTKGroup ↥H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ)) (hns : ¬ Group.IsSolvable ↥H) :
    B69.BlkCtx (autI hV H) (autI hV T) (autI hV M) := by
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set Γ) := fun hle =>
    hJ ((thompsonJ_le_self T).trans (h.isSylow.1.trans hle))
  have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set Γ) := fun hle =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf h.isSylow).trans hle)
  obtain ⟨hFF, -⟩ := B2_7_of_not_le hV hred.1 hred.2.1 hJH
  exact blkCtx_of_inputs hP4 hComp (fun v : IntMod V hV => IntMod.sq_eq_one v)
    (sqtk_star hV hsq hred.2.1) (minParabolic_star hV h hred hHV) (pCoreOf_star hV hred) hFF
    (not_isSolvable_star hV h hred hHV hns)

end Glue

end GE23

end CFSG.Quasithin
