module

public import CFSG.Quasithin.EmptyFaithful.S146G1
public import CFSG.Quasithin.EmptyFaithful.S14113Stage
public import CFSG.Quasithin.EmptyFaithful.S146Lem2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.Quasithin.EmptyFaithful.S146A1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_oTwoFstarIn (H : Subgroup G) :
    H ≤ Subgroup.normalizer (oTwoFstarIn H : Set G) := by
  rw [← map_O2Fstar_eq_oTwoFstarIn]
  have : (CFSG.layer (OTwoQuot H)).Characteristic := CFSG.LocalCores.layer_characteristic
  have : (CFSG.generalizedFitting (OTwoQuot H)).Normal := by
    simp only [CFSG.generalizedFitting.eq_sup]
    infer_instance
  exact normalizer_preimH (N := CFSG.generalizedFitting (OTwoQuot H))

theorem le_pCoreOf_of_oTwoFstarIn_le {H : Subgroup G} (h : oTwoFstarIn H ≤ pCoreOf 2 H) :
    H ≤ pCoreOf 2 H := by
  have hF : CFSG.generalizedFitting (OTwoQuot H) = ⊥ := by
    rw [← imageOTwoQuot_O2Fstar H, map_O2Fstar_eq_oTwoFstarIn]
    refine eq_bot_iff.mpr ?_
    rintro _ ⟨⟨y, hyH⟩, hy, rfl⟩
    have hyQ : y ∈ pCoreOf 2 H := h (Subgroup.mem_subgroupOf.mp hy)
    obtain ⟨z, hz, hzy⟩ := hyQ
    have : z = ⟨y, hyH⟩ := Subtype.ext hzy
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).mpr (this ▸ hz)
  have hc := CFSG.centralizer_generalizedFitting_le (OTwoQuot H)
  rw [hF] at hc
  intro x hx
  have h1 : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) ⟨x, hx⟩ : OTwoQuot H) ∈
      (⊥ : Subgroup (OTwoQuot H)) := by
    refine hc ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hz
    rw [hz]
    simp
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

theorem stage1461Six_of (h2 : Stage1461Two) (h3 : Stage1461Three) (h5 : Stage1461Five) :
    Stage1461Six := by
  intro G _ _ T M S H hH T₁ hQT₁ hT₁T hT₁n
  have hTH : T ≤ H := hH.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hT₁2 : IsPGroup 2 T₁ := hT2.to_le hT₁T
  have hT₁ne : T₁ ≠ ⊥ := fun h => hH.1.2 (le_bot_iff.mp (h ▸ hQT₁))
  have hchar : ((omegaOneCenterOf T₁).subgroupOf T₁).Characteristic :=
    CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T₁
  have hZ₁T₁ : omegaOneCenterOf T₁ ≤ T₁ := A4.omegaOneCenterOf_le T₁
  have hN : Subgroup.normalizer (T₁ : Set G) ≤ Subgroup.normalizer (omegaOneCenterOf T₁ : Set G) :=
    normalizer_le_normalizer_of_characteristic_subgroupOf hZ₁T₁ hchar
  refine ⟨hN, ?_⟩
  set Z₁ := omegaOneCenterOf T₁ with hZ₁
  set Q := pCoreOf 2 H with hQ
  have hUQ : conjClosure (VZ T M) H ≤ Q :=
    (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.toHypF91.conjClosure_Vp_le_pCoreOf
  have hZ₁W : Z₁ ≤ omegaOneCenterOf Q := by
    refine (Subgroup.closure_le _).mpr fun z hz => ?_
    have hzT₁ : z ∈ T₁ := hz.1.1
    have hzC : z ∈ Subgroup.centralizer (T₁ : Set G) := hz.1.2
    have hzCQ : z ∈ Subgroup.centralizer (Q : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQT₁) hzC
    have hzCU : z ∈ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUQ) hzCQ
    have hzQ : z ∈ Q := S.inf_centralizer_le_pCoreOf hH ⟨hTH (hT₁T hzT₁), hzCU⟩
    exact Subgroup.subset_closure ⟨⟨hzQ, hzCQ⟩, hz.2⟩
  have hYZ : oTwoFstarIn H ≤ Subgroup.centralizer (Z₁ : Set G) :=
    (h5 G T M S H hH).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZ₁W))
  have hTN : T ≤ Subgroup.normalizer (Z₁ : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hT₁T).mp hT₁n).trans hN
  set Y := oTwoFstarIn H with hY
  have hYH : Y ≤ H := oTwoFstarIn_le H
  have hYn : H ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_oTwoFstarIn H
  set X := oTwoUpper Y with hX
  have hXY : X ≤ Y := oTwoUpper_le Y
  have hXH : X ≤ H := hXY.trans hYH
  have hXO : oTwoUpper X = X := S146A.oTwoUpper_idem Y
  have hXn : (X.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr
      (hYn.trans (normalizer_le_normalizer_oTwoUpper Y))
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hY2 : IsPGroup 2 Y := by
      refine isPGroup_two_of_forall fun y hy => ?_
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper Y hy
      rw [← hX, hbot, Subgroup.mem_bot] at hk
      exact ⟨k, hk⟩
    have hYQ : Y ≤ Q := le_pCoreOf_of_le_normalizer 2 hYH hYn hY2
    have hHQ : H ≤ Q := le_pCoreOf_of_oTwoFstarIn_le hYQ
    have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH)
    exact hH.2 (hHQ.trans (hQT.trans hTM))
  have hXT : IsHTM T M (X ⊔ T) := stage1461Four_of h2 h3 G T M S H hH X hXne hXO hXH hXn
  have hXZ : X ≤ Subgroup.normalizer (Z₁ : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer (Z₁ : Set G) (hYZ (hXY hx))
  have hZ₁ne : Z₁ ≠ ⊥ := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hT₁2 hT₁ne
  have hZ₁2 : IsPGroup 2 Z₁ := hT₁2.to_le hZ₁T₁
  have hloc : IsTwoLocal (Subgroup.normalizer (Z₁ : Set G)) := ⟨Z₁, hZ₁ne, hZ₁2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq : M' = mcOf T :=
    (S.isUniqueM_mcOf hXT).2 M' ⟨hM', (sup_le hXZ hTN).trans hle⟩
  rw [← hM'eq]
  exact hle

end CFSG.Quasithin
