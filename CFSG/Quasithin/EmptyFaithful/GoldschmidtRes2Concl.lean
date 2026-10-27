module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2D11
public import CFSG.Quasithin.Vol2.Ch3y319

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T Mc M K N : Subgroup G}

theorem NonBorelK.concl319 (hD125 : D125NonsolvableSQTK) (h : quasithinQTFE14Cat G T Mc)
    (hMf : IsMf T Mc M) (h158 : Lemma1518Concl T Mc M) (h159 : Lemma1519Concl T Mc M)
    (hK : NonBorelK T Mc M K N) (hVK : V154 T Mc M ≤ pCoreOf 2 K) {c : ℕ} (hc2 : 2 ≤ c)
    (hser : IsChiefSeriesFrom K (conjClosure (V154 T Mc M) K) (conjClosure (V154 T Mc M) K) c) :
    Concl319 T M (V154 T Mc M) K False := by
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
  have hUe := D15Proof.isElemAbelian_conjClosure hD hnff hVK
  have hD125' := d125_of_input hD125 hD hsq hq1 hVK hUe
  have hq2 : (2 : WithTop ℚ) ≤ qInt M₀ V hV := hq2'.ge
  have hc : c = 2 := Ch3y.c_eq_two hD hnff hVK hD125' hq2 hc2 hser
  subst hc
  have hRT : pCoreOf 2 K ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hK.minParabolic.isSylow
  have hUT := conjClosure_le_T hD hVK
  have hTH : T ≤ K := hK.T_le_K
  have hchain : ∀ A : Subgroup G, IsMinOffender T K V A →
      (Subgroup.centralizer (conjClosure V K : Set G)).relIndex (pCoreOf 2 K ⊓ A) =
        (pCoreOf 2 K).relIndex A ∧
      (Subgroup.centralizer (A : Set G)).relIndex (conjClosure V K) =
        ((pCoreOf 2 K).relIndex A) ^ 2 ∧
      (Subgroup.centralizer ((pCoreOf 2 K ⊓ A : Subgroup G) : Set G)).relIndex (conjClosure V K) =
        ((pCoreOf 2 K).relIndex A) ^ 2 ∧
      (∀ L N : Subgroup G, IsChiefStep K (conjClosure V K) L N → ¬ IsCentralStep K L N →
        (centralizerMod L N A).relIndex N = (pCoreOf 2 K).relIndex A ∧
          centralizerMod L A N = pCoreOf 2 K ⊓ A) ∧
      (∀ k ∈ K, ¬ (pCoreOf 2 K ⊓ A) ≤ Subgroup.centralizer (cjSub k V : Set G) →
        ((Subgroup.centralizer (cjSub k V : Set G)).relIndex (pCoreOf 2 K ⊓ A)) ^ 2 =
          (Subgroup.centralizer ((pCoreOf 2 K ⊓ A : Subgroup G) : Set G)).relIndex
            (cjSub k V)) := by
    intro A hA
    obtain ⟨-, hb, hu, hv, hst, hcj⟩ := Ch3y.chain_two hD hnff hVK hD125' hq2 le_rfl hser
      hA.1.1 hA.1.2.1 hA.2.2.2 (not_le_centralizer_conjClosure hD hnff hA.1.1 (hA.not_le hRT))
      (card_le_relIndex_mul_card hUe hUT hA.1)
    exact ⟨hb, hu, hv, hst, hcj⟩
  refine
    { elemAbelian := hUe
      chief := hser
      exists_A := LRed13.exists_isMinOffender_quadratic hD hnff hVK hq2
      quadratic := fun A hA => hA.2.2.2
      count_one := fun A hA => count_one_of (hchain A hA).2.1
      count_two := fun A hA => ?_
      count_three := fun A hA k hk hne => ?_
      count_four := fun A hA L N hstep hnc => ?_
      fixed_eq := fun A hA => ?_
      shape := fun hf => hf.elim }
  · have hb := (hchain A hA).1
    have hu := (hchain A hA).2.1
    exact count_two_of hu hb
  · have hBW : ¬ (pCoreOf 2 K ⊓ A) ≤ Subgroup.centralizer (cjSub k⁻¹ V : Set G) := by
      rw [inf_comm]
      intro hle
      exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)
    have heq := (hchain A hA).2.2.2.2 k⁻¹ (K.inv_mem hk) hBW
    rw [inf_comm (pCoreOf 2 K) A] at heq
    exact count_three_of (B := A ⊓ pCoreOf 2 K) (W := conjSubgroup V k) heq
  · obtain ⟨hu₀, hD'⟩ := (hchain A hA).2.2.2.1 L N hstep hnc
    have hL : IsNormalIn K (conjClosure V K) L := hstep.2.1
    have hNH : N ≤ K := hstep.1.1.trans (hUT.trans hTH)
    refine ⟨?_, ?_⟩
    · rw [cSecIn_eq_centralizerMod (U := conjClosure V K) (H := K) (hA.1.1.trans hTH) hL, hD',
        inf_comm]
    · rw [fixSecIn_eq_centralizerMod (U := conjClosure V K) hNH hL]
      exact count_four_of (centralizerMod_le_left L N A) hu₀
  · have hu := (hchain A hA).2.1
    have hv := (hchain A hA).2.2.1
    rw [inf_comm (pCoreOf 2 K) A] at hv
    exact inf_eq_of_relIndex_eq (Subgroup.centralizer_le fun x hx => (Subgroup.mem_inf.mp hx).1)
      (hu.trans hv.symm)

end CFSG.Quasithin.Gap6R2
