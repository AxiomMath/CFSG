module

public import CFSG.Quasithin.EmptyFaithful.S153E55F
public import CFSG.Quasithin.Background.F9Section
public import CFSG.Quasithin.Background.S1549CBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1549C

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem comm_ZS_of_adm (h11 : StageLemma14111) (h113 : StageLemma14113)
    (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G} (hH : Adm T Mc M H) :
    ⁅ZS153 T M V₁, pCoreOf 2 H⁆ = quasithinOmegaOneCenter T := by
  classical
  have h := cx.c.hyp
  have hF := cx.hF91 h113 hH
  have hHH := hH.hH
  have hZ2 := h.lemma_15_3_2_two.2
  have hHMc : H ≤ Mc := C1Pack153.le_mc_of_isHTM153 h11 h hHH
  have hHZ : H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    hHMc.trans (h.lemma_15_3_4 h11).le
  have hle : ⁅ZS153 T M V₁, pCoreOf 2 H⁆ ≤ quasithinOmegaOneCenter T := by
    refine Subgroup.commutator_le.mpr fun u hu q hq => ?_
    have := hF.commutator_conjClosure_le u (le_conjClosure (ZS153 T M V₁) H hu) q hq
    rwa [commutatorElement_def]
  rcases HypF98.eq_bot_or_eq_of_card_eq_two hZ2 hle with hbot | heq
  swap
  · exact heq
  exfalso
  have hZsC : ZS153 T M V₁ ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hQC : pCoreOf 2 H ≤ Subgroup.centralizer (ZS153 T M V₁ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hbot)
  have hUQ : conjClosure (ZS153 T M V₁) H ≤ pCoreOf 2 H := hF.conjClosure_Vp_le_pCoreOf
  have hUC : conjClosure (ZS153 T M V₁) H ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    refine conjClosure_le fun k hk z hz => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    have hq' : k⁻¹ * q * k ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hk)) q).mp hq
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (hQC hq') z hz
    calc q * (k * z * k⁻¹) = k * ((k⁻¹ * q * k) * z) * k⁻¹ := by group
      _ = k * (z * (k⁻¹ * q * k)) * k⁻¹ := by rw [← h1]
      _ = (k * z * k⁻¹) * q := by group
  have hUel : IsElemAbelian 2 (conjClosure (ZS153 T M V₁) H) := by
    refine HypF91.isElemAbelian_conjClosure_of_forall hF.elemAbelian_Vp fun k hk => ?_
    exact hZsC.trans (Subgroup.centralizer_le ((HypF91.conjSub_le_conjClosure hk).trans hUQ))
  have hUΩ : conjClosure (ZS153 T M V₁) H ≤ omegaOneCenterOf (pCoreOf 2 H) := fun u hu =>
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hUQ hu, hUC hu, isElemAbelian_pow_eq_one hUel hu⟩
  have hFst := C1Pack.oTwoFstarIn_le_centralizer_omegaOneCenter h.qtfe.qtke h.qtfe.sylow
    h.qtfe.faithful_empty hHH.1 hHZ
  have hFQ : oTwoFstarIn H ≤ pCoreOf 2 H := by
    intro x hx
    have hxH : x ∈ H := Subgroup.map_subtype_le _ hx
    rw [hF.pCoreOf_eq_centralizerMod]
    refine ⟨hxH, (Subgroup.centralizer_le_normalizer _) (hHZ hxH), fun u hu => ?_⟩
    have hc := Subgroup.mem_centralizer_iff.mp (hFst hx) u (hUΩ hu)
    have : x * u * x⁻¹ * u⁻¹ = 1 := by rw [← hc]; group
    rw [this]
    exact Subgroup.one_mem _
  have hMcle : H ≤ pCoreOf 2 H := C1Pack153.le_pCoreOf_of_oTwoFstarIn_le' hFQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH2 : IsPGroup 2 H := (pCoreOf_isPGroup 2 H).to_le hMcle
  have hHT : H ≤ T := by
    refine A4.le_of_normal_of_isSylowTwoOf hF.sylow_H le_rfl ?_ hH2
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  exact hHH.2 (hHT.trans h.T_le)

theorem exists_mul_of_mem_sup_of_le_normalizer {K : Type*} [Group K] {A B : Subgroup K}
    (hB : B ≤ Subgroup.normalizer (A : Set K)) {g : K} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let S : Subgroup K :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a * (b * a' * b⁻¹), A.mul_mem ha
          ((Subgroup.mem_normalizer_iff.mp (hB hb) a').mp ha'), b * b', B.mul_mem hb hb',
          by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b, ?_, b⁻¹, B.inv_mem hb, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hB (B.inv_mem hb)) a⁻¹).mp (A.inv_mem ha)
        simpa using this }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hg

theorem claim_m (h11 : StageLemma14111) (h113 : StageLemma14113)
    (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G} (hH : Adm T Mc M H)
    (hc : omegaOneOf (pCoreOf 2 H) ≤ Sgp153 T V₁ ∧
      UH T M V₁ H ≤ centerOf (omegaOneOf (pCoreOf 2 H))) :
    UH T M V₁ H ⊔ VZ T M < VH T M H := by
  classical
  have h := cx.c.hyp
  have D := cx.c.decomp
  have hF := cx.hF91 h113 hH
  have hHH := hH.hH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hF.sylow_H
  have hTH : T ≤ H := hF.T_le_H
  have hVT : VZ T M ≤ T := h.VZ_le_T
  have hVN : T ≤ Subgroup.normalizer (VZ T M : Set G) := h.T_le.trans h.le_normalizer
  have hUsupV : UH T M V₁ H ⊔ VZ T M ≤ VH T M H :=
    sup_le (conjClosure_mono inf_le_left le_rfl) (le_conjClosure _ _)
  refine lt_of_le_of_ne hUsupV ?_
  intro heq
  have hVHle : VH T M H ≤ UH T M V₁ H ⊔ VZ T M := heq.symm.le
  have hVnormU : VZ T M ≤ Subgroup.normalizer (UH T M V₁ H : Set G) :=
    hVT.trans (hTH.trans (le_normalizer_conjClosure _ _))
  have hΩ : ∀ g, g ∈ VZ T M → g ∈ pCoreOf 2 H → g ∈ omegaOneOf (pCoreOf 2 H) := fun g hgV hgQ =>
    Subgroup.subset_closure ⟨hgQ, h.elemAbelian.2 g hgV⟩
  have hc1 : ∀ w ∈ VH T M H, ∀ q ∈ pCoreOf 2 H, w * q * w⁻¹ * q⁻¹ ∈ VZ T M := by
    intro w hw q hq
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hVnormU (hVHle hw)
    have hcV : v * q * v⁻¹ * q⁻¹ ∈ VZ T M := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hVN (hQT hq)) v⁻¹).mp ((VZ T M).inv_mem hv)
      have e : v * q * v⁻¹ * q⁻¹ = v * (q * v⁻¹ * q⁻¹) := by group
      rw [e]
      exact (VZ T M).mul_mem hv h1
    have hcQ : v * q * v⁻¹ * q⁻¹ ∈ pCoreOf 2 H := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hTH (hVT hv))) q).mp hq
      exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hq)
    have hcu : (v * q * v⁻¹ * q⁻¹) * u = u * (v * q * v⁻¹ * q⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hc.2 hu).2 _ (hΩ _ hcV hcQ)
    have huq : u * q * u⁻¹ * q⁻¹ ∈ quasithinOmegaOneCenter T :=
      hF.commutator_conjClosure_le u hu q hq
    have e : u * v * q * (u * v)⁻¹ * q⁻¹ =
        (v * q * v⁻¹ * q⁻¹) * (u * q * u⁻¹ * q⁻¹) := by
      have e1 : u * (v * q * v⁻¹ * q⁻¹) * u⁻¹ = v * q * v⁻¹ * q⁻¹ := by
        calc u * (v * q * v⁻¹ * q⁻¹) * u⁻¹ = (u * (v * q * v⁻¹ * q⁻¹)) * u⁻¹ := rfl
          _ = ((v * q * v⁻¹ * q⁻¹) * u) * u⁻¹ := by rw [← hcu]
          _ = v * q * v⁻¹ * q⁻¹ := by group
      calc u * v * q * (u * v)⁻¹ * q⁻¹
          = (u * (v * q * v⁻¹ * q⁻¹) * u⁻¹) * (u * q * u⁻¹ * q⁻¹) := by group
        _ = (v * q * v⁻¹ * q⁻¹) * (u * q * u⁻¹ * q⁻¹) := by rw [e1]
    rw [e]
    exact (VZ T M).mul_mem hcV (h.Z_le_VZ huq)
  have hZsQ := comm_ZS_of_adm h11 h113 cx hH
  have hZne : quasithinOmegaOneCenter T ≠ ⊥ := by
    intro hb
    have := h.lemma_15_3_2_two.2
    rw [hb, Subgroup.card_bot] at this
    omega
  have hVQ : ¬ pCoreOf 2 H ≤ Subgroup.centralizer (VZ T M : Set G) := by
    intro hle
    have h1 : ⁅ZS153 T M V₁, pCoreOf 2 H⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (Subgroup.mem_centralizer_iff.mp (hle hq) z hz.1).symm
    rw [hZsQ] at h1
    exact hZne h1
  obtain ⟨q₀, hq₀Q, hq₀V⟩ : ∃ q ∈ pCoreOf 2 H, q ∉ Subgroup.centralizer (VZ T M : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hVQ hcon
  have hQN : pCoreOf 2 H ≤ Subgroup.normalizer (VZ T M : Set G) := hQT.trans hVN
  have hq₀N : q₀ ∈ Subgroup.normalizer (VZ T M : Set G) := hQN hq₀Q
  have hV := h.elemAbelian
  obtain ⟨hV', L₁, L₂, tb, hS, hV₁, hV₂, -⟩ := D.model
  obtain ⟨s₁, s₂, τ, a₁, a₂, hFs⟩ := hS.exists_sylowFacts h.isSylowTwoOf_autI
  have hQbarT : autI hV (pCoreOf 2 H) ≤ autI hV T := autI_mono hV hQT
  have hQnorm : ∀ x ∈ autI hV T, ∀ n ∈ autI hV (pCoreOf 2 H), x * n * x⁻¹ ∈ autI hV (pCoreOf 2 H) := by
    intro x hx n hn
    obtain ⟨t', ht'T, rfl⟩ := (mem_autI hV).1 hx
    obtain ⟨q, hqQ, rfl⟩ := (mem_autI hV).1 hn
    have hmem : (t' : G) * q * (t' : G)⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hTH ht'T)) q).mp hqQ
    exact (mem_autI hV).2 ⟨t' * q * t'⁻¹, hmem, by simp [map_mul]⟩
  have hq₀1 : convI hV ⟨q₀, hq₀N⟩ ≠ 1 := fun h1 => hq₀V ((convI_eq_one_iff hV _).mp h1)
  have hrQ : s₁ * s₂ ∈ autI hV (pCoreOf 2 H) :=
    S153E.mul_mem_of_normal_ne_bot hS h.isSylowTwoOf_autI hFs hQbarT hQnorm
      ⟨convI hV ⟨q₀, hq₀N⟩, convI_mem_autI hV hq₀Q hq₀N, hq₀1⟩
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (VZ T M : Set G) := inf_le_left.trans hVN
  have hexp' : ∀ w : IntMod (VZ T M) hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hrr : (s₁ * s₂) * (s₁ * s₂) = 1 := by
    calc (s₁ * s₂) * (s₁ * s₂) = s₁ * (s₂ * s₁) * s₂ := by group
      _ = s₁ * (s₁ * s₂) * s₂ := by rw [hFs.comm]
      _ = (s₁ * s₁) * (s₂ * s₂) := by group
      _ = 1 := by rw [hFs.s₁_sq, hFs.s₂_sq, one_mul]
  have hfr : Nat.card ↥(fixV (Subgroup.zpowers (s₁ * s₂))) = 4 :=
    S153E.card_fixV_mul_s hexp' hS hFs.sylow
  have hrS : s₁ * s₂ ∈ autI hV T ⊓ (L₁ ⊔ L₂) := (hFs.S_eq _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hfix : fixV (Subgroup.zpowers (s₁ * s₂)) = fixV (autI hV T ⊓ (L₁ ⊔ L₂)) :=
    (Subgroup.eq_of_le_of_card_ge (fixV_anti (Subgroup.zpowers_le.mpr hrS))
      (by rw [hfr, hFs.card_fix])).symm
  have hcommfix : commV (Subgroup.zpowers (s₁ * s₂)) = fixV (Subgroup.zpowers (s₁ * s₂)) :=
    S153E55.commV_zpowers_eq_fixV hexp' h.card_VZ hrr hfr
  have hSbar := S153E.autI_Sgp153 (T := T) (M := M) hV hS h.T_le hV₁.symm
  have hZsle : ZS153 T M V₁ ≤ (commV (Subgroup.zpowers (s₁ * s₂))).map (inclMod hV) := by
    intro z hz
    refine ⟨IntMod.mk hV ⟨z, hz.1⟩, ?_, rfl⟩
    rw [hcommfix, hfix, ← hSbar]
    exact (mem_fixV_autI hV hSN _).2 hz.2
  have hbar_le : commV (Subgroup.zpowers (s₁ * s₂)) ≤ commV (autI hV (pCoreOf 2 H)) :=
    Subgroup.closure_mono fun _ ⟨a, ha, v, hv⟩ =>
      ⟨a, (Subgroup.zpowers_le.mpr hrQ) ha, v, hv⟩
  have hZsVQ : ZS153 T M V₁ ≤ ⁅VZ T M, pCoreOf 2 H⁆ := by
    rw [S1417.commutator_eq_map_commV hV hQN]
    exact hZsle.trans (Subgroup.map_mono hbar_le)
  set U' : Subgroup G := ⁅VH T M H, pCoreOf 2 H⁆ with hU'
  have hU'V : U' ≤ VZ T M := Subgroup.commutator_le.mpr fun w hw q hq => by
    have := hc1 w hw q hq
    rwa [commutatorElement_def]
  have hVQU' : ⁅VZ T M, pCoreOf 2 H⁆ ≤ U' := Subgroup.commutator_mono (le_conjClosure _ _) le_rfl
  have hZsU' : ZS153 T M V₁ ≤ U' := hZsVQ.trans hVQU'
  have hHU' : H ≤ Subgroup.normalizer (U' : Set G) :=
    F9.le_normalizer_commutator_of_le (le_normalizer_conjClosure _ _) (le_normalizer_pCoreOf 2 H)
  obtain ⟨a, ha, ha1, -⟩ := exists_gen_inf_centralizer_Sgp153 h D
  have haZs : a ∈ ZS153 T M V₁ := ⟨D.le₁ ha.1, ha.2⟩
  have haU' : a ∈ U' := hZsU' haZs
  by_cases hUV : U' = VZ T M
  · apply hHH.2
    have hM : M = Subgroup.normalizer (VZ T M : Set G) := h.isHv_of_inM' h.inM
    rw [hM]
    rw [hUV] at hHU'
    exact hHU'
  · have hlt : U' < VZ T M := lt_of_le_of_ne hU'V hUV
    have hbot : ⊥ < U' := bot_lt_iff_ne_bot.mpr fun hb =>
      ha1 (by rw [hb] at haU'; exact Subgroup.mem_bot.mp haU')
    have hnot : ¬ Subgroup.normalizer (U' : Set G) ≤ M := fun hle => hHH.2 (hHU'.trans hle)
    have hts := cx.r46.totSingular_of_normalizer U' hU'V hbot hlt hnot
    have : a ∈ U' ⊓ V₁ := ⟨haU', ha.1⟩
    rw [hts.2.1, Subgroup.mem_bot] at this
    exact ha1 this

end S1549C

end CFSG.Quasithin
