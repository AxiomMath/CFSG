module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Red
public import CFSG.Quasithin.Vol2.GoldschmidtE217L33Mult
public import CFSG.Quasithin.Vol2.GoldschmidtE217L33Pair
public import CFSG.Quasithin.Vol2.GoldschmidtE217L33Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M E217R3

namespace E217R4

theorem r3Pkg2d3 :
    R3Pkg2d3 := by
  intro G _ _ H T M V K hS _ hC2 hL _ _
  have h := hS.toHyp2
  have hmp := h.hyp.minParabolic
  have hJ : kerIn M H = pCoreOf 2 H := kerIn_eq_pCoreOf_of_L33 hS hC2 hL
  have hL' : CFSG.GH74.E2.ShapeL33 ↥(E2.star M H K) := by
    unfold CFSG.GH74.E2.ShapeL33 CFSG.Blueprint.LieModel
    exact Or.inl ⟨by decide, hL⟩
  have hfacts := CFSG.GH74.E2.ShapeL33.facts hL'
  have hsimp : IsSimpleGroup ↥(E2.star M H K) := hfacts.1
  have hZ : Subgroup.center ↥(E2.star M H K) = ⊥ := by
    have := hfacts.1
    exact CFSG.GH74.E2.center_eq_bot_of_simple_of_not_prime hfacts.2.2
  have hX := asHyp_star' hmp hS.mem_cComp hS.eq_sup hC2 hsimp hZ
    (nonab_star' (M := M) hS.mem_cComp)
  obtain ⟨x, hxH, hxV, hxQ, hv2, hv1, -, hvM, -⟩ := exists_vbar_aux h
  have hStarTM : E2.star M H T ≤ E2.star M H M :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hmp.le)
  obtain ⟨A, T₀, hA9, hT₀T, hT₀A, hirr, hvT₀, hvinv⟩ := l33_pair hX.normal hX.cent
    hX.minPar.isSylow hL' hv2 hv1 fun t ht => hvM t (hStarTM ht)
  have hker : ∀ w : ↥H, E2P.starMap M H w = 1 ↔ (w : G) ∈ pCoreOf 2 H := fun w => by
    rw [← hJ]
    have : w ∈ (E2P.starMap M H).ker ↔ (w : G) ∈ kerIn M H := by
      rw [E2P.ker_starMap]
      exact Subgroup.mem_subgroupOf
    exact this
  have hVT₀ : (V.subgroupOf H).map (E2P.starMap M H) ≤ T₀ := by
    rintro _ ⟨y, hy, rfl⟩
    rcases E2.forall_mem_or_mul_mem_of_relIndex_eq_two h.hyp.elem h.two hxV hxQ (y : G) hy
      with hq | hq
    · rw [(hker y).2 hq.2]
      exact T₀.one_mem
    · have h3 : E2P.starMap M H ⟨x, hxH⟩ * E2P.starMap M H y = 1 := by
        rw [← map_mul]
        exact (hker _).2 hq.2
      have h4 : E2P.starMap M H y = E2P.starMap M H ⟨x, hxH⟩ := by
        rw [eq_inv_of_mul_eq_one_right h3]
        exact inv_eq_of_mul_eq_one_right hv2
      rw [h4]
      exact hvT₀
  exact false_of_star h.hyp h.charTwo h.q32 h.V16 hJ hA9 hT₀T hT₀A hirr hxV hVT₀ hvinv

end E217R4

end CFSG.Quasithin
