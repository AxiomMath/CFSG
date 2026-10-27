module

public import CFSG.Quasithin.Vol2.GoldschmidtE217B1A6Pair
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Borel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M E217R3

namespace E217R4

theorem r3Pkg2bOne_A6
    {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G} (hS : Setting2 H T M V K)
    (hC2 : Case2 H T M K) (hA6 : IsAlt 6 ↥(E2.star M H K))
    (hdiag : E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K))) :
    False := by
  have hmp := hS.toHyp2.hyp.minParabolic
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimp : IsSimpleGroup ↥(E2.star M H K) := hA6.some.isSimpleGroup
  have hnab := nonab_star' (M := M) hS.mem_cComp
  have hX := asHyp_star' hmp hS.mem_cComp hS.eq_sup hC2 hsimp (OL.center_eq_bot_of_simple hnab)
    hnab
  obtain ⟨v, hv2, hv1, -, hvM, hodd⟩ := exists_vbar hS.toHyp2
  have hStarTM : E2.star M H T ≤ E2.star M H M :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hmp.le)
  have hTK : E2.star M H (T ⊓ K) = E2.star M H T ⊓ E2.star M H K :=
    E2P.star_inf_T hmp.isSylow hS.mem_cComp.2.2.1 hKH
  exact a6_false hX.normal hX.cent hX.minPar.isSylow hA6 hv2 hv1
    (fun t ht => hvM t (hStarTM ht)) hodd fun P hP hle => hdiag P hP (by rw [hTK]; exact hle)

end E217R4

end CFSG.Quasithin
