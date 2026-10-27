module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2Shape
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Main
public import CFSG.Quasithin.EmptyFaithful.Gap6R2Equiv

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T Mc M K N : Subgroup G}

theorem NonBorelK.core_of_concl319 (h : quasithinQTFE14Cat G T Mc) (hK : NonBorelK T Mc M K N)
    (hVK : V154 T Mc M ≤ pCoreOf 2 K) (hc : Concl319 T M (V154 T Mc M) K True) :
    ⁅omegaOneCenterOf (thompsonJi T 1), oTwoUpper K⁆ = ⊥ := by
  have hmp : MinParabolic K T N := hK.minParabolic
  have hTH : T ≤ K := hK.T_le_K
  have hQT : pCoreOf 2 K ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow
  obtain ⟨A, hA⟩ := hc.exists_A
  obtain ⟨L, N', hst, hnc, -⟩ := S152Fin.exists_noncentral_of_series hc.chief (by norm_num : 1 ≤ 2)
  have hshape := hc.shape trivial L N' hst hnc
  have hK' : ¬ oTwoUpper K ≤ cSecIn K L N' := S152L08.not_oTwoUpper_le_cSecIn hst hshape
  have hctx : X1512.ShapeCtx T N K (conjClosure (V154 T Mc M) K) L N' A :=
    ⟨hmp, hc.elemAbelian, hst, hnc, hA.1.1, hA.1.2.1, X1512.not_le_pCoreOf_of_isMinOffender hQT hA,
      hc.count_four A hA L N' hst hnc,
      B6.le_thompsonJ (B6.isMaxElemAbelian_of_sylow hmp.isSylow hA.1)⟩
  obtain ⟨x, hxH, hxP, hx3, hxA, hxinv⟩ := X1512.shapeDatum_of_shape hctx hK' hshape
  obtain ⟨X, hXP, hXH, hAX, hAQ, hQTX, hP1, hP2, hHX⟩ :=
    X1512.exists_X hmp (S152Fin.cSecIn_le_left K L N') hctx.normalizes hctx.pCoreOf_le hK' hA.1.1
      hA.1.2.1 hxH hxP hx3 hxA hxinv
  exact Der6A.core1512Four_gen h.sylow hTH hVK hc.elemAbelian hA (hc.count_one A hA)
    (hc.count_two A hA) (by simpa using hc.fixed_eq A hA) hXP hXH hAX hAQ hQTX hP1 hP2 hHX

theorem NonBorelK.outcome4_false (hB69 : B69Struct) (hB1 : B69One) (hD125 : D125NonsolvableSQTK)
    (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M) (h157 : Lemma1517Concl T Mc M)
    (h15 : Lemma1515Concl T Mc M) (h158 : Lemma1518Concl T Mc M) (h159 : Lemma1519Concl T Mc M)
    (hK : NonBorelK T Mc M K N)
    (hmin : ∀ L : Subgroup G, T ≤ L → L < K →
      oTwoUpper L ≤ Subgroup.centralizer (vE T Mc M : Set G))
    (hVK : V154 T Mc M ≤ pCoreOf 2 K) {c : ℕ} (hc2 : 2 ≤ c)
    (hser : IsChiefSeriesFrom K (conjClosure (V154 T Mc M) K) (conjClosure (V154 T Mc M) K) c) :
    False := by
  have hmain : Concl319 T M (V154 T Mc M) K False := hK.concl319 hD125 h hMf h158 h159 hVK hc2 hser
  have hshape := hK.chiefFactorShape hB69 hB1 hD125 h hMf h158 h159 hmin hVK hc2 hser
  have hc' : Concl319 T M (V154 T Mc M) K True := { hmain with shape := fun _ => hshape }
  have hE := hK.core_of_concl319 h hVK hc'
  have hVE := vE_le_omegaOneCenter_J1 h hMf h157 h15 h159
  exact hK.not_oTwoUpper_le ((le_centralizer_of_commutator_eq_bot hE).trans
    (Subgroup.centralizer_le hVE))

end CFSG.Quasithin.Gap6R2
