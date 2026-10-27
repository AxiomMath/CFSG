module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Five
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Wr
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Core
public import CFSG.Quasithin.EmptyFaithful.LRed9Quad
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Build

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace X1512

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_le_pCoreOf_of_isMinOffender {T H V A : Subgroup G} (hQT : pCoreOf 2 H ≤ T)
    (hA : IsMinOffender T H V A) : ¬ A ≤ pCoreOf 2 H := fun hle =>
  hA.2.1 ⟨hle, hA.1.2.1, fun B hBQ hB => hA.1.2.2 B (hBQ.trans hQT) hB⟩

theorem shapeDatum_of_shape {T P H U L N A : Subgroup G} (c : ShapeCtx T P H U L N A)
    (hK : ¬ oTwoUpper H ≤ cSecIn H L N) (hshape : ChiefFactorShape H L N) :
    ShapeDatum H P (cSecIn H L N) A := by
  obtain ⟨hNorm, h3 | h5 | w3 | w5⟩ := hshape
  · have := hNorm
    exact shapeDatum_nat (Or.inl rfl) c hK h3.2
  · have := hNorm
    exact shapeDatum_nat (Or.inr rfl) c hK h5.2
  · have := hNorm
    exact shapeDatum_wr (Or.inl rfl) c hK w3.1 w3.2
  · have := hNorm
    exact shapeDatum_wr (Or.inr rfl) c hK w5.1 w5.2

theorem core_of_concl319 {T Mc M H : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hCE : IsCE1513 T M) (h159 : Lemma1519Concl T Mc M)
    (hH : IsHStar T M H) (hVH : V154 T Mc M ≤ pCoreOf 2 H)
    (hc : Concl319 T M (V154 T Mc M) H True) :
    ⁅omegaOneCenterOf (thompsonJi T 1), oTwoUpper H⁆ = ⊥ := by
  have hs : Setting152 T Mc M := ⟨h, hM, hCE⟩
  have hmp : MinParabolic H T (H ⊓ M) :=
    S152L08.minParabolic_of_hStar hs hH h159.seven_normalizer
  have hTH : T ≤ H := hH.1.1
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow
  obtain ⟨A, hA⟩ := hc.exists_A
  obtain ⟨L, N, hst, hnc, -⟩ := S152Fin.exists_noncentral_of_series hc.chief (by norm_num : 1 ≤ 2)
  have hshape := hc.shape trivial L N hst hnc
  have hK : ¬ oTwoUpper H ≤ cSecIn H L N := S152L08.not_oTwoUpper_le_cSecIn hst hshape
  have hctx : ShapeCtx T (H ⊓ M) H (conjClosure (V154 T Mc M) H) L N A :=
    ⟨hmp, hc.elemAbelian, hst, hnc, hA.1.1, hA.1.2.1, not_le_pCoreOf_of_isMinOffender hQT hA,
      hc.count_four A hA L N hst hnc,
      B6.le_thompsonJ (B6.isMaxElemAbelian_of_sylow hmp.isSylow hA.1)⟩
  obtain ⟨x, hxH, hxP, hx3, hxA, hxinv⟩ := shapeDatum_of_shape hctx hK hshape
  obtain ⟨X, hXP, hXH, hAX, hAQ, hQTX, hP1, hP2, hHX⟩ :=
    exists_X hmp (S152Fin.cSecIn_le_left H L N) hctx.normalizes hctx.pCoreOf_le hK hA.1.1 hA.1.2.1
      hxH hxP hx3 hxA hxinv
  exact Der6A.core1512Four_gen h.sylow hTH hVH hc.elemAbelian hA (hc.count_one A hA)
    (hc.count_two A hA) (by simpa using hc.fixed_eq A hA) hXP hXH hAX hAQ hQTX hP1 hP2 hHX

end X1512

namespace LRed9

theorem stageLemma15112Four_of_gen (h319 : Lemma319StatementCE) (h1416 : StageLemma1416)
    (h1515 : StageLemma1515CE) (h158 : StageLemma1518) (h159 : StageLemma1519)
    (h16 : StageLemma1516CE) (h1511one : StageLemma15111One) : StageLemma15112Four := by
  intro G _ _ T Mc M h hM hCE H hH
  have hVH : V154 T Mc M ≤ pCoreOf 2 H := h1511one G T Mc M h hM hCE H hH
  have hc : Concl319 T M (V154 T Mc M) H True :=
    lemma_15_1_12_concl319 h319 h hM hCE (h158 G T Mc M h hM hCE) (h159 G T Mc M h hM hCE)
      (h16 G T Mc M h hM hCE) (notDualFF1512_of_ce h1416 h1515 h158 h159 G T Mc M h hM hCE) hH hVH
  exact X1512.core_of_concl319 h hM hCE (h159 G T Mc M h hM hCE) hH hVH hc

end LRed9

end CFSG.Quasithin
