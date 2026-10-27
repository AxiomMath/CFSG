module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2D11
public import CFSG.Quasithin.EmptyFaithful.Gap6R2Red
public import CFSG.Quasithin.Vol2.Ch3g316Red
public import CFSG.Quasithin.Vol2.Ch3nCore
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD14Proof

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T Mc M K N : Subgroup G}

theorem NonBorelK.false_of_sylow (hC58 : TheoremC58) (h : quasithinQTFE14Cat G T Mc)
    (hMf : IsMf T Mc M) (h159 : Lemma1519Concl T Mc M) (hK : NonBorelK T Mc M K N)
    (hS : IsSylowTwoOf (pCoreOf 2 (m0 T Mc M)) (oTwoUpper K ⊔ pCoreOf 2 (m0 T Mc M))) : False := by
  refine hK.not_inf_le_centralizer hC58 h hMf h159 ?_
  have hR : pCoreOf 2 (m0 T Mc M) = T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    h159.six_pCore
  have hRT : pCoreOf 2 (m0 T Mc M) ≤ T := hR ▸ inf_le_left
  exact (inf_le_of_isSylowTwoOf_sup hRT h.sylow.1 hS).trans (hR ▸ inf_le_right)

theorem NonBorelK.outcome5_false (hC58 : TheoremC58) (hB1 : B69One) (h1413 : StageLemma1413)
    (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M) (h158 : Lemma1518Concl T Mc M)
    (h159 : Lemma1519Concl T Mc M) (hND : ¬ IsDualFFOn (m0 T Mc M) (V154 T Mc M))
    (hK : NonBorelK T Mc M K N) (hVK : V154 T Mc M ≤ pCoreOf 2 K)
    (h5a : ((pCoreOf 2 (m0 T Mc M) ⊓ pCoreOf 2 K).subgroupOf K).Normal)
    (h5b : IsElemAbelian 2 (conjClosure (V154 T Mc M) K))
    (h5c : IsChiefSeriesFrom K (conjClosure (V154 T Mc M) K) (conjClosure (V154 T Mc M) K) 1) :
    False := by
  set V := V154 T Mc M with hVdef
  set M₀ := m0 T Mc M with hM₀
  have hTM : T ≤ M := hMf.1.1.2
  have hD : D11Hyp M₀ K T V N := hK.d11Hyp h hMf h159
  have hV : IsElemAbelian 2 V := hD.reduced.2.2.1
  have hKH : InH T K := hK.inH h
  have hsq : IsSQTKSub K := isSQTKSub_of_inH h.qtke h.simple h.nonabelian hKH
  have hchar : CharTwo K := charTwo_of_inH' h.qtke h.sylow hKH
  have hnff : ¬ IsFFInt M₀ V hV := fun hff => by
    have h1 := (isFFInt_iff_qInt_le_one _ _ _).mp hff
    rw [qInt_m0 h159 h158 hV] at h1
    norm_num at h1
  have hdual : ¬ IsDualFFInt M₀ V hV := fun hd => hND ⟨hV, hd⟩
  by_cases hsolv : Group.IsSolvable K
  · exact hK.false_of_sylow hC58 h hMf h159
      (EmptyFaithfulMultiple.inputD14Solvable_holds G M₀ K T V N hD hVK h5c hdual hsolv hchar)
  · have hmp : MinParabolic K T N := hK.minParabolic
    have hTK : T ≤ K := hK.T_le_K
    have hRT : pCoreOf 2 M₀ ≤ T := hD.pCoreOf_le_T
    have hTR : T ≤ Subgroup.normalizer ((pCoreOf 2 M₀ : Subgroup G) : Set G) :=
      (T_le_m0 hTM).trans (le_normalizer_pCoreOf 2 M₀)
    have hJR : thompsonJ T ≤ pCoreOf 2 M₀ := hD.thompsonJ_le hnff
    have hJH : ¬ thompsonJ T ≤ pCoreOf 2 K := hK.not_thompsonJ_le_pCoreOf h h159
    have hVR : V ≤ pCoreOf 2 M₀ := A4.le_pCoreOf_of_isTwoReducedIn hD.reduced
    have hQH : pCoreOf 2 M₀ ⊓ pCoreOf 2 K ≤ K := inf_le_right.trans (pCoreOf_le 2 K)
    have hQnorm : K ≤ Subgroup.normalizer ((pCoreOf 2 M₀ ⊓ pCoreOf 2 K : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp h5a
    have hRC : pCoreOf 2 M₀ ≤ Subgroup.centralizer (V : Set G) := by
      rw [hD.centralizer]
      exact inf_le_right
    have hUQ : conjClosure V K ≤ pCoreOf 2 M₀ ⊓ pCoreOf 2 K := by
      refine conjClosure_le fun g hg v hv => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hQnorm hg) v).mp ⟨hVR hv, hVK hv⟩
    have hUC : conjClosure V K ≤
        Subgroup.centralizer ((pCoreOf 2 M₀ ⊓ pCoreOf 2 K : Subgroup G) : Set G) := by
      refine conjClosure_le fun g hg v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro q hq'
      have hq1 : g⁻¹ * q * g ∈ pCoreOf 2 M₀ ⊓ pCoreOf 2 K := by
        have := (Subgroup.mem_normalizer_iff.mp (hQnorm (K.inv_mem hg)) q).mp hq'
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp (hRC hq1.1) v hv
      calc q * (g * v * g⁻¹) = g * ((g⁻¹ * q * g) * v) * g⁻¹ := by group
        _ = g * (v * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
        _ = (g * v * g⁻¹) * q := by group
    by_cases hKU : twoResidual K ≤ Subgroup.centralizer (conjClosure V K : Set G)
    · have hKV : twoResidual K ≤ Subgroup.centralizer (V : Set G) :=
        hKU.trans (Subgroup.centralizer_le fun v hv => le_conjClosure _ _ hv)
      have hTKR : T ⊓ twoResidual K ≤ pCoreOf 2 M₀ := by
        rw [hD.centralizer]
        exact inf_le_inf_left T hKV
      have := Ch3n.isSylowTwoOf_sup_of_inf_le hmp.isSylow (twoResidual_le K)
        (le_normalizer_twoResidual K) hRT hTKR
      rw [F6.twoResidual_eq_oTwoUpper] at this
      exact hK.false_of_sylow hC58 h hMf h159 this
    · obtain ⟨hred, hJ'⟩ := Ch3g316.exists_reducedModule hB1 hmp hsq hRT hTR hJR hJH hQnorm h5b
        (le_normalizer_conjClosure V K) hUQ hUC hKU
      have hKI : ¬ K ≤ Subgroup.centralizer ((⁅conjClosure V K, twoResidual K⁆ : Subgroup G) :
          Set G) := fun hle => hJ' ((B6.thompsonJ_le T).trans (hTK.trans hle))
      exact hsolv (C1Pack.isSolvable_of_perfectCore_le hmp hred hKI
        (h1413 G T h.simple h.qtke h.sylow h.faithful_empty K hKH _ hred))

theorem NonBorelK.qrc (hC58 : TheoremC58) (hB1 : B69One) (h1413 : StageLemma1413)
    (hD15 : D15AsPrintedSQTK) (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M)
    (h158 : Lemma1518Concl T Mc M) (h159 : Lemma1519Concl T Mc M)
    (hND : ¬ IsDualFFOn (m0 T Mc M) (V154 T Mc M)) (hK : NonBorelK T Mc M K N) :
    ¬ V154 T Mc M ≤ pCoreOf 2 K ∨
      (V154 T Mc M ≤ pCoreOf 2 K ∧ IsElemAbelian 2 (conjClosure (V154 T Mc M) K) ∧
        ∃ c : ℕ, 2 ≤ c ∧ IsChiefSeriesFrom K (conjClosure (V154 T Mc M) K)
          (conjClosure (V154 T Mc M) K) c) := by
  by_cases hVK : V154 T Mc M ≤ pCoreOf 2 K
  swap
  · exact Or.inl hVK
  right
  refine ⟨hVK, ?_⟩
  set V := V154 T Mc M with hVdef
  set M₀ := m0 T Mc M with hM₀
  have hD : D11Hyp M₀ K T V N := hK.d11Hyp h hMf h159
  have hV : IsElemAbelian 2 V := hD.reduced.2.2.1
  have hKH : InH T K := hK.inH h
  have hsq : IsSQTKSub K := isSQTKSub_of_inH h.qtke h.simple h.nonabelian hKH
  have hq2 : qInt M₀ V hV = 2 := qInt_m0 h159 h158 hV
  have hnff : ¬ IsFFInt M₀ V hV := fun hff => by
    have h1 := (isFFInt_iff_qInt_le_one _ _ _).mp hff
    rw [hq2] at h1
    norm_num at h1
  have hUe : IsElemAbelian 2 (conjClosure V K) :=
    D15Proof.isElemAbelian_conjClosure hD hnff hVK
  refine ⟨hUe, ?_⟩
  rcases hD15 G M₀ K T V N hD hsq with h1 | ⟨h2, -⟩ | h3 | ⟨-, -, c, hc2, hc⟩ |
      ⟨h5a, h5b, h5c, -, -, -⟩
  · exact absurd hVK h1
  · rw [hq2] at h2
    norm_num at h2
  · exact absurd ⟨hV, h3⟩ hND
  · exact ⟨c, hc2, hc⟩
  · exact (hK.outcome5_false hC58 hB1 h1413 h hMf h158 h159 hND hVK h5a h5b h5c).elim

end CFSG.Quasithin.Gap6R2
