module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2Concl
public import CFSG.Quasithin.EmptyFaithful.E23JShape
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T Mc M K N : Subgroup G}

omit [Finite G] in
theorem isChiefStep_of_le {K U' U L N' : Subgroup G} (hU'U : U' ≤ U)
    (h : IsChiefStep K U' L N') : IsChiefStep K U L N' := by
  obtain ⟨⟨hN'U', hN'n⟩, ⟨hLU', hLn⟩, hLN, hmax⟩ := h
  refine ⟨⟨hN'U'.trans hU'U, hN'n⟩, ⟨hLU'.trans hU'U, hLn⟩, hLN, fun X hX hLX hXN => ?_⟩
  exact hmax X ⟨hXN.trans hN'U', hX.2⟩ hLX hXN

theorem NonBorelK.setting_of_quadratic (hD125 : D125NonsolvableSQTK)
    (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M) (h158 : Lemma1518Concl T Mc M)
    (h159 : Lemma1519Concl T Mc M) (hK : NonBorelK T Mc M K N)
    (hVK : V154 T Mc M ≤ pCoreOf 2 K)
    (hser : IsChiefSeriesFrom K (conjClosure (V154 T Mc M) K) (conjClosure (V154 T Mc M) K) 2)
    {D : Subgroup G} (hDT : IsMaxElemAbelian T D) (hDn : ¬ D ≤ pCoreOf 2 K)
    (hDq : ⁅⁅conjClosure (V154 T Mc M) K, D⁆, D⁆ = ⊥) :
    Ch3z.Setting K T N (conjClosure (V154 T Mc M) K) D := by
  set V := V154 T Mc M with hVdef
  set M₀ := m0 T Mc M with hM₀
  have hD : D11Hyp M₀ K T V N := hK.d11Hyp h hMf h159
  have hV : IsElemAbelian 2 V := hD.reduced.2.2.1
  have hKH : InH T K := hK.inH h
  have hsq : IsSQTKSub K := isSQTKSub_of_inH h.qtke h.simple h.nonabelian hKH
  have hq2' : qInt M₀ V hV = 2 := qInt_m0 h159 h158 hV
  have hnff : ¬ IsFFInt M₀ V hV := fun hff => by
    have h1 := (isFFInt_iff_qInt_le_one _ _ _).mp hff
    rw [hq2'] at h1
    norm_num at h1
  have hq1 : ¬ qInt M₀ V hV ≤ 1 := by
    rw [hq2']
    norm_num
  have hq2 : (2 : WithTop ℚ) ≤ qInt M₀ V hV := hq2'.ge
  have hmp : MinParabolic K T N := hK.minParabolic
  have hUe := D15Proof.isElemAbelian_conjClosure hD hnff hVK
  have hD125' := d125_of_input hD125 hD hsq hq1 hVK hUe
  have hUT := conjClosure_le_T hD hVK
  have hTH : T ≤ K := hK.T_le_K
  have hDnc := not_le_centralizer_conjClosure hD hnff hDT.1 hDn
  obtain ⟨-, -, -, -, hst, -⟩ := Ch3y.chain_two hD hnff hVK hD125' hq2 le_rfl hser
    hDT.1 hDT.2.1 hDq hDnc (card_le_relIndex_mul_card hUe hUT hDT)
  refine ⟨hmp, hsq, hUT, hUe, hDT, hDn, fun L N' hstep hnc => ?_⟩
  obtain ⟨hu₀, hD'⟩ := hst L N' hstep hnc
  have hL : IsNormalIn K (conjClosure V K) L := hstep.2.1
  have hNH : N' ≤ K := hstep.1.1.trans (hUT.trans hTH)
  refine ⟨?_, ?_⟩
  · rw [cSecIn_eq_centralizerMod (U := conjClosure V K) (H := K) (hDT.1.trans hTH) hL, hD',
      inf_comm]
  · rw [fixSecIn_eq_centralizerMod (U := conjClosure V K) hNH hL]
    exact count_four_of (centralizerMod_le_left L N' D) hu₀

theorem NonBorelK.chiefFactorShape (hB69 : B69Struct) (hB1 : B69One) (hD125 : D125NonsolvableSQTK)
    (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M) (h158 : Lemma1518Concl T Mc M)
    (h159 : Lemma1519Concl T Mc M) (hK : NonBorelK T Mc M K N)
    (hmin : ∀ L : Subgroup G, T ≤ L → L < K →
      oTwoUpper L ≤ Subgroup.centralizer (vE T Mc M : Set G))
    (hVK : V154 T Mc M ≤ pCoreOf 2 K) {c : ℕ} (hc2 : 2 ≤ c)
    (hser : IsChiefSeriesFrom K (conjClosure (V154 T Mc M) K) (conjClosure (V154 T Mc M) K) c) :
    ∀ L N' : Subgroup G, IsChiefStep K (conjClosure (V154 T Mc M) K) L N' → ¬ IsCentralStep K L N' →
      ChiefFactorShape K L N' := by
  intro L N' hstep hnc
  have hmain : Concl319 T M (V154 T Mc M) K False := hK.concl319 hD125 h hMf h158 h159 hVK hc2 hser
  set V := V154 T Mc M with hVdef
  set M₀ := m0 T Mc M with hM₀
  have hTM : T ≤ M := hMf.1.1.2
  have hD : D11Hyp M₀ K T V N := hK.d11Hyp h hMf h159
  have hV : IsElemAbelian 2 V := hD.reduced.2.2.1
  have hKH : InH T K := hK.inH h
  have hsq : IsSQTKSub K := isSQTKSub_of_inH h.qtke h.simple h.nonabelian hKH
  have hq2' : qInt M₀ V hV = 2 := qInt_m0 h159 h158 hV
  have hnff : ¬ IsFFInt M₀ V hV := fun hff => by
    have h1 := (isFFInt_iff_qInt_le_one _ _ _).mp hff
    rw [hq2'] at h1
    norm_num at h1
  have hq1 : ¬ qInt M₀ V hV ≤ 1 := by
    rw [hq2']
    norm_num
  have hq2 : (2 : WithTop ℚ) ≤ qInt M₀ V hV := hq2'.ge
  have hmp : MinParabolic K T N := hK.minParabolic
  have hUe : IsElemAbelian 2 (conjClosure V K) := hmain.elemAbelian
  have hD125' := d125_of_input hD125 hD hsq hq1 hVK hUe
  have hUT : conjClosure V K ≤ T := conjClosure_le_T hD hVK
  have hTH : T ≤ K := hK.T_le_K
  have hRT : pCoreOf 2 K ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow
  have hser2 : IsChiefSeriesFrom K (conjClosure V K) (conjClosure V K) 2 := hmain.chief
  obtain ⟨A, hA⟩ := hmain.exists_A
  have hset : Ch3z.Setting K T N (conjClosure V K) A :=
    ⟨hmp, hsq, hUT, hUe, hA.1, hA.not_le hRT,
      fun L' N'' hs' hnc' => hmain.count_four A hA L' N'' hs' hnc'⟩
  have hrepl : ∀ A' : Subgroup G, IsMaxElemAbelian T A' → ¬ A' ≤ pCoreOf 2 K →
      ∃ D : Subgroup G, Ch3z.Setting K T N (conjClosure V K) D ∧ D ≤ A' ⊔ conjClosure V K := by
    intro A' hA' hA'R
    have hA'n : ¬ IsMaxElemAbelian (pCoreOf 2 K) A' := fun hmax => hA'R hmax.1
    obtain ⟨D, hDT, hDn, hDq, hDA⟩ := E23J.exists_quadratic_below hD hnff hVK hq2 hA' hA'n
    exact ⟨D, hK.setting_of_quadratic hD125 h hMf h158 h159 hVK hser2 hDT hDn hDq, hDA⟩
  set W := vE T Mc M with hWdef
  have hWV : W ≤ V := inf_le_left
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := T_le_normalizer_vE hTM
  set UW := conjClosure W K with hUWdef
  have hUWU : UW ≤ conjClosure V K := conjClosure_le fun g hg w hw =>
    Subgroup.subset_closure ⟨g, hg, w, hWV hw, rfl⟩
  have hUWT : UW ≤ T := hUWU.trans hUT
  have hUWe : IsElemAbelian 2 UW := Setup.Campbell.isElemAbelian_mono hUe hUWU
  have hUWn : IsNormalIn K UW UW :=
    ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure W K hg) x).mp hx⟩
  have hgenW : ∀ W' : Subgroup G, IsNormalIn K UW W' → W ≤ W' → UW ≤ W' :=
    fun W' hW' hWW' => conjClosure_le fun g hg z hz => hW'.2 g hg z (hWW' hz)
  obtain ⟨n, hn⟩ := D15Proof.exists_isChiefSeriesFrom (H := K) (U := UW) UW hUWn
  have hn0 : n ≠ 0 := by
    intro h0
    have hcomm := D14.commutator_eq_bot_of_zero (hmp.isSylow.2.1.to_le hUWT) hn h0
    apply hK.not_oTwoUpper_le
    have hle : oTwoUpper K ≤ Subgroup.centralizer (UW : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm
    exact hle.trans (Subgroup.centralizer_le (le_conjClosure W K))
  obtain ⟨L₁, N₁, hs₁, hnc₁, -⟩ :=
    S152Fin.exists_noncentral_of_series hn (Nat.one_le_iff_ne_zero.mpr hn0)
  obtain ⟨L₀, N₀, hstep₀', hnc₀, z, hzW, hzN, hzL, hzT⟩ := Ch3z.exists_good_step hmp.isSylow hUWT
    hUWe (le_normalizer_conjClosure W K) (le_conjClosure W K) hgenW hTW ⟨L₁, N₁, hs₁, hnc₁⟩
  have hstep₀ : IsChiefStep K (conjClosure V K) L₀ N₀ := isChiefStep_of_le hUWU hstep₀'
  have hodd : ∀ d ∈ N, Odd (orderOf d) → d * z * d⁻¹ * z⁻¹ ∈ L₀ := by
    intro d hd ho
    have hdC : d ∈ Subgroup.centralizer (W : Set G) :=
      hmin N hK.T_le_N hK.N_lt_K (mem_oTwoUpper_of_odd hd ho)
    have hcomm := Subgroup.mem_centralizer_iff.mp hdC z hzW
    have e : d * z * d⁻¹ * z⁻¹ = 1 := by
      rw [← hcomm]
      group
    rw [e]
    exact L₀.one_mem
  obtain ⟨χ₀, hχC, a, haA, haH, hχa⟩ := hset.good hB69 hB1 hstep₀ hnc₀ hzN hzL hzT hodd
  exact E23J.chiefFactorShape_of_setting' hB69 hB1 hset hrepl hstep₀ hnc₀ hχC haA haH hχa hstep hnc

end CFSG.Quasithin.Gap6R2
