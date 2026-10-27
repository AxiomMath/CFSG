module

public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.EmptyFaithful.T1531Gold2
public import CFSG.Quasithin.EmptyFaithful.S153Five
public import CFSG.Quasithin.EmptyFaithful.S153Baum

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

structure Res15367Two {G : Type} [Group G] (T M E : Subgroup G) : Prop where
  sylow_GE : IsSylowTwoOf (TE153 T E) (Subgroup.normalizer (E : Set G))
  baum_le : baum (TE153 T E) ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G)
  CGS_le : CGS (baum (TE153 T E)) ≤ M

structure Res15367Rest {G : Type} [Group G] (T Mc M E : Subgroup G) : Prop where
  R_eq : T ⊓ Subgroup.centralizer (VZ T M : Set G) = Subgroup.centralizer (VZ T M : Set G)
  M_eq : M = Y153 Mc M ⊔ T
  GE_eq : Subgroup.normalizer (E : Set G) = (YE153 Mc M E ⊔ XE153 E) ⊔ TE153 T E
  XE_not_le : ¬ XE153 E ≤ M
  XE_quot : Nonempty (OTwoQuot (XE153 E) ≃* Multiplicative (ZMod 3))
  YE_quot : Nonempty (OTwoQuot (YE153 Mc M E) ≃* Multiplicative (ZMod 3))
  YE_normal : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (YE153 Mc M E : Set G)
  XE_normal : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (XE153 E : Set G)
  quot_S3S3 : Nonempty (OTwoQuot (Subgroup.normalizer (E : Set G)) ≃*
    Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  XE_comm : XE153 E = ⁅XE153 E, thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G))⁆

theorem Res15367.of_parts {G : Type} [Group G] {T Mc M V₁ V₂ E : Subgroup G}
    (h2 : Res15367Two T M E) (hr : Res15367Rest T Mc M E) : Res15367 T Mc M V₁ V₂ E where
  R_eq := hr.R_eq
  M_eq := hr.M_eq
  sylow_GE := h2.sylow_GE
  baum_le := h2.baum_le
  CGS_le := h2.CGS_le
  GE_eq := hr.GE_eq
  XE_not_le := hr.XE_not_le
  XE_quot := hr.XE_quot
  YE_quot := hr.YE_quot
  YE_normal := hr.YE_normal
  XE_normal := hr.XE_normal
  quot_S3S3 := hr.quot_S3S3
  XE_comm := hr.XE_comm

namespace C1Pack153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

omit [Finite G] in
theorem R_le_TE (L : LineData153 T M V₁ V₂ E) :
    T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ TE153 T E :=
  inf_le_inf_left T ((Subgroup.centralizer_le L.le_V).trans (Subgroup.centralizer_le_normalizer _))

theorem V_le_TE (h : Hyp153 G T Mc M) (L : LineData153 T M V₁ V₂ E) : VZ T M ≤ TE153 T E := by
  refine le_inf h.VZ_le_T fun v hv => ?_
  refine (Subgroup.centralizer_le_normalizer _) (Subgroup.mem_centralizer_iff.mpr fun e he => ?_)
  exact F7.isElemAbelian_comm h.elemAbelian (L.le_V he) hv

omit [Finite G] in
theorem TE_conj_mem (r66 : Res15366B T Mc M V₁ V₂ E) {g x : G} (hg : g ∈ T)
    (hx : x ∈ TE153 T E) : g * x * g⁻¹ ∈ TE153 T E := by
  have hi : ((TE153 T E).subgroupOf T).index = 2 := r66.relIndex_two
  have hn : ((TE153 T E).subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hi
  have := hn.conj_mem ⟨x, (inf_le_left : TE153 T E ≤ T) hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem thompsonJ_TE_le_centralizer (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) :
    thompsonJ (TE153 T E) ≤ Subgroup.centralizer (VZ T M : Set G) := by
  classical
  have h := c.hyp
  have hMN := h.le_normalizer
  have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := h.T_le.trans hMN
  have hTEle : TE153 T E ≤ T := inf_le_left
  have hVTE := V_le_TE h L
  obtain ⟨hV', L₁, L₂, tb, hS, rfl, rfl, -⟩ := c.decomp.model
  have hsyl : IsSylowTwoOf (autI hV' T) (autI hV' M) := h.isSylowTwoOf_autI
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF, hoff⟩ := hS.offender_classification hsyl
  refine iSup₂_le fun A hA => ?_
  by_contra hAC
  have hAT : A ≤ TE153 T E := hA.1
  have hAN : A ≤ Subgroup.normalizer (VZ T M : Set G) := hAT.trans (hTEle.trans hTN)
  have hBne : autI hV' A ≠ ⊥ := (autI_eq_bot_iff hV' hAN).not.2 hAC
  have hBab : IsElemAbelian2 (autI hV' A) := isElemAbelian2_autI hV' hA.2.1 hAN
  have hBT : autI hV' A ≤ autI hV' T := autI_mono hV' (hAT.trans hTEle)
  have hineq := card_le_relIndex_mul_card hV' hVTE hA
  have hff : Nat.card (IntMod (VZ T M) hV') ≤
      Nat.card (autI hV' A) * Nat.card (fixV (autI hV' A)) := by
    rw [card_autI_eq hV' hAN, card_fixV_autI hV' hAN]
    exact hineq
  obtain ⟨-, hs⟩ := hoff (autI hV' A) hBT hBne hBab hff
  have hτT : τ ∈ autI hV' T := hF.τ_T
  have hconj : ∀ x ∈ autI hV' (TE153 T E), τ * x * τ⁻¹ ∈ autI hV' (TE153 T E) := by
    intro x hx
    obtain ⟨g, hgT, rfl⟩ := (mem_autI hV').1 hτT
    obtain ⟨k, hkE, rfl⟩ := (mem_autI hV').1 hx
    refine (mem_autI hV').2 ⟨g * k * g⁻¹, TE_conj_mem r66 hgT hkE, ?_⟩
    simp [map_mul, map_inv]
  have hsE : s₁ ∈ autI hV' (TE153 T E) ∨ s₂ ∈ autI hV' (TE153 T E) :=
    hs.imp (fun h1 => autI_mono hV' hAT h1) (fun h1 => autI_mono hV' hAT h1)
  have hboth : s₁ ∈ autI hV' (TE153 T E) ∧ s₂ ∈ autI hV' (TE153 T E) := by
    rcases hsE with h1 | h2
    · refine ⟨h1, ?_⟩
      have := hconj s₁ h1
      rwa [hF.τs₁] at this
    · refine ⟨?_, h2⟩
      have := hconj s₂ h2
      rwa [hF.τs₂] at this
  have hle : autI hV' T ⊓ (L₁ ⊔ L₂) ≤ autI hV' (TE153 T E) := by
    intro x hx
    rcases (hF.S_eq x).1 hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hboth.1
    · exact hboth.2
    · exact Subgroup.mul_mem _ hboth.1 hboth.2
  have hS4 : Nat.card ↥(autI hV' T ⊓ (L₁ ⊔ L₂)) = 4 := hS.card_S hsyl
  have hTE4 : Nat.card ↥(autI hV' (TE153 T E)) = 4 := r66.barTE_klein.1.1
  have hSbar := autI_nS hV' hS h.T_le
  have heq : autI hV' T ⊓ (L₁ ⊔ L₂) = autI hV' (TE153 T E) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hS4, hTE4])
  exact r66.barTE_klein.2 (heq.symm.trans hSbar.symm)

theorem V_le_omegaOneCenter_thompsonJ (h : Hyp153 G T Mc M) :
    VZ T M ≤ omegaOneCenterOf (thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G))) := by
  classical
  have hV := h.elemAbelian
  have hVR : VZ T M ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    le_inf h.VZ_le_T fun v hv => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      F7.isElemAbelian_comm hV ha hv
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian (T ⊓ Subgroup.centralizer (VZ T M : Set G))
  have hVA : ∀ A, IsMaxElemAbelian (T ⊓ Subgroup.centralizer (VZ T M : Set G)) A →
      VZ T M ≤ A := by
    intro A hA
    have hAC : A ≤ Subgroup.centralizer (VZ T M : Set G) := hA.1.trans inf_le_right
    have hel : IsElemAbelian 2 (VZ T M ⊔ A) :=
      B2F.isElemAbelian_sup_of_commute hV hA.2.1 fun v hv a ha =>
        Subgroup.mem_centralizer_iff.mp (hAC ha) v hv
    have hcard := hA.2.2 (VZ T M ⊔ A) (sup_le hVR hA.1) hel
    exact (Subgroup.eq_of_le_of_card_ge le_sup_right hcard) ▸ le_sup_left
  have hJC : thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤
      Subgroup.centralizer (VZ T M : Set G) := (thompsonJ_le_self _).trans inf_le_right
  intro v hv
  have hA₀J : A₀ ≤ thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G)) :=
    le_iSup₂_of_le A₀ hA₀ le_rfl
  refine Subgroup.subset_closure ⟨⟨hA₀J (hVA A₀ hA₀ hv), ?_⟩, hV.2 v hv⟩
  refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hJC hj) v hv).symm

theorem res15367Two (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) : Res15367Two T M E := by
  classical
  have h := c.hyp
  have hV := h.elemAbelian
  have hRTE : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ TE153 T E := R_le_TE L
  have hJ : thompsonJ (TE153 T E) ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    le_inf ((thompsonJ_le_self _).trans inf_le_left) (thompsonJ_TE_le_centralizer c L r66)
  have hJeq : thompsonJ (TE153 T E) =
      thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G)) := thompsonJ_eq_of_le hJ hRTE
  have hVΩ : VZ T M ≤ omegaOneCenterOf (thompsonJ (TE153 T E)) :=
    hJeq ▸ V_le_omegaOneCenter_thompsonJ h
  have hbaum_le : baum (TE153 T E) ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    intro x hx
    exact ⟨hx.1.1, Subgroup.centralizer_le hVΩ hx.2⟩
  have hbaumEq : baum (TE153 T E) = baum (T ⊓ Subgroup.centralizer (VZ T M : Set G)) :=
    baum_eq_of_le hbaum_le hRTE
  have hRn : Y153 Mc M ⊔ T ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) := by
    obtain ⟨he, hn⟩ := h.R153_Y153 h113 c.decomp
    rw [he] at hn
    exact hn
  have hbR : baum (T ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤
      T ⊓ Subgroup.centralizer (VZ T M : Set G) := inf_le_left
  have hYTb : Y153 Mc M ⊔ T ≤
      Subgroup.normalizer
        ((baum (T ⊓ Subgroup.centralizer (VZ T M : Set G)) : Subgroup G) : Set G) :=
    hRn.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hbR
      (C1GN.characteristic_baum _))
  have hU := h.lemma_15_3_7_unique h113
  have hCGS : CGS (baum (TE153 T E)) ≤ M := by
    rw [hbaumEq]
    refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hchar => ?_
    have hNC : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
      hYTb.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hCR hchar)
    have hCp : IsPGroup 2 C :=
      h.qtfe.sylow.1.to_le (hCR.trans (hbR.trans inf_le_left))
    have hCO : C ≤ pCoreOf 2 (Subgroup.normalizer (C : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hCp
    exact le_of_isUniqueM hU ⟨hNC, fun hb => hC1 (le_bot_iff.mp (hb ▸ hCO))⟩
  have hVB : VZ T M ≤ baum (TE153 T E) := by
    intro v hv
    refine ⟨V_le_TE h L hv, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hwR : w ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
      hJ (A4.omegaOneCenterOf_le _ hw)
    exact (Subgroup.mem_centralizer_iff.mp hwR.2 v hv).symm
  have hBne : baum (TE153 T E) ≠ ⊥ := by
    intro hb
    have h1 : Nat.card (VZ T M) = 1 := by
      rw [Subgroup.card_eq_one]
      exact eq_bot_iff.mpr (hb ▸ hVB)
    have := h.card_VZ
    omega
  have hNB : Subgroup.normalizer (baum (TE153 T E) : Set G) ≤ M := by
    have hch : ((baum (TE153 T E)).subgroupOf (baum (TE153 T E))).Characteristic := by
      rw [Subgroup.subgroupOf_self]
      infer_instance
    have : Subgroup.normalizer (baum (TE153 T E) : Set G) ≤ CGS (baum (TE153 T E)) :=
      le_iSup₂_of_le (baum (TE153 T E)) le_rfl (le_iSup₂_of_le hBne hch le_rfl)
    exact this.trans hCGS
  have hNTE : Subgroup.normalizer (TE153 T E : Set G) ≤ M :=
    (normalizer_le_normalizer_of_characteristic_subgroupOf (inf_le_left : baum (TE153 T E) ≤ _)
      (C1GN.characteristic_baum _)).trans hNB
  have hSyl : IsSylowTwoOf (TE153 T E) (Subgroup.normalizer (E : Set G) ⊓ M) := by
    rw [inf_comm]
    exact L.sylow
  exact ⟨isSylowTwoOf_of_normalizer_le (inf_le_right : TE153 T E ≤ _) hNTE hSyl, hbaum_le, hCGS⟩

end C1Pack153

@[expose] def Stage15367Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
      Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367Two T M E →
        Res15367Rest T Mc M E

theorem stage15367B_of_rest (h113 : StageLemma14113) (i : Stage15367Rest) : Stage15367B := by
  intro G _ _ T Mc M V₁ V₂ E t c r45 r46 r49 r50 L r66
  have h2 := C1Pack153.res15367Two h113 c L r66
  exact Res15367.of_parts h2 (i G T Mc M V₁ V₂ E t c r45 r46 r49 r50 L r66 h2)

end CFSG.Quasithin
