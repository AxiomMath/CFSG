module

public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.EmptyFaithful.S153Sub
public import CFSG.Quasithin.EmptyFaithful.S153Y

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

abbrev Sgp153 {G : Type} [Group G] (T V₁ : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.normalizer (V₁ : Set G)

@[expose] def Cases15310 {G : Type} [Group G] (T Mc M V₁ Yp : Subgroup G) : Prop :=
  Yp = Y153 Mc M ∨
    (IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
      Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)))

structure Hyp15310 (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G) :
    Prop where
  hyp : Hyp153 G T Mc M
  decomp : Decomp153 T M V₁ V₂ t
  cases : Cases15310 T Mc M V₁ Yp

abbrev MI153 {G : Type} [Group G] (M I : Subgroup G) : Subgroup G := M ⊓ I

abbrev UI153 {G : Type} [Group G] (T I : Subgroup G) : Subgroup G :=
  conjClosure (quasithinOmegaOneCenter T) I

abbrev R153 {G : Type} [Group G] (T V₁ Yp : Subgroup G) : Subgroup G :=
  pCoreOf 2 (Yp ⊔ Sgp153 T V₁)

@[expose] def IsHPlus {G : Type} [Group G] (Yp S M I : Subgroup G) : Prop :=
  InH (Yp ⊔ S) I ∧ ¬ I ≤ M

section General

variable {G : Type} [Group G] [Finite G]

theorem le_of_isUniqueM {X M H : Subgroup G} (hU : IsUniqueM X M) (hH : InH X H) : H ≤ M := by
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hH.2
  have h1 : M' = M := hU.2 M' ⟨hM'.1, hH.1.trans hM'.2⟩
  exact h1 ▸ hM'.2

end General

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem T_le_normalizer_Sgp153 (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) := by
  have hidx : (Sgp153 T V₁).relIndex T = 2 := D.relIndex_nS h
  have hS : Sgp153 T V₁ ≤ T := inf_le_left
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hS).mp
    (Subgroup.normal_of_index_eq_two hidx)

theorem lemma_15_3_11_twelve (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    {L : Subgroup G} (hL : ⁅VZ T M, oTwoUpper (Y153 Mc M ⊓ L)⁆ ≠ ⊥) (hLM : ¬ L ≤ M)
    {C : Subgroup G} (hCS : C ≤ Sgp153 T V₁) (hC1 : C ≠ ⊥)
    (hchar : (C.subgroupOf (Sgp153 T V₁)).Characteristic) :
    ¬ (L ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (C : Set G)) := by
  intro hN
  have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
    (h.T_le_normalizer_Sgp153 D).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hCS hchar)
  have hY₁L : oTwoUpper (Y153 Mc M ⊓ L) ≤ L := (oTwoUpper_le _).trans inf_le_right
  have hY₁M : oTwoUpper (Y153 Mc M ⊓ L) ≤ M :=
    (oTwoUpper_le _).trans (inf_le_left.trans (Y153_le Mc M))
  have hXN : oTwoUpper (Y153 Mc M ⊓ L) ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    sup_le ((hY₁L.trans le_sup_left).trans hN) hTC
  have hXM : oTwoUpper (Y153 Mc M ⊓ L) ⊔ T ≤ M := sup_le hY₁M h.T_le
  rcases h.lemma_15_3_2_four (le_sup_right : T ≤ oTwoUpper (Y153 Mc M ⊓ L) ⊔ T) hXM with
    hi | ⟨-, hU⟩
  · apply hL
    have hres : oTwoUpper (Y153 Mc M ⊓ L) ≤ opResidual 2 (oTwoUpper (Y153 Mc M ⊓ L) ⊔ T) := by
      rw [oTwoUpper, Subgroup.closure_le]
      intro x hx
      exact Subgroup.subset_closure ⟨Subgroup.mem_sup_left (mem_oTwoUpper_of_odd hx.1 hx.2),
        Nat.coprime_two_right.mpr hx.2⟩
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv y hy
    have hyc := Subgroup.mem_centralizer_iff.mp (hi (hres hy)) v hv
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr hyc)
  · have hCp : IsPGroup 2 C := (h.qtfe.sylow.1).to_le (hCS.trans inf_le_left)
    have hCO : C ≤ pCoreOf 2 (Subgroup.normalizer (C : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hCp
    have hH : InH (oTwoUpper (Y153 Mc M ⊓ L) ⊔ T) (Subgroup.normalizer (C : Set G)) :=
      ⟨hXN, fun hbot => hC1 (le_bot_iff.mp (hbot ▸ hCO))⟩
    exact hLM ((le_sup_left.trans hN).trans (le_of_isUniqueM hU hH))

theorem VZ_eq_conjClosure_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    VZ T M = conjClosure (quasithinOmegaOneCenter T) (Y153 Mc M) := by
  have hV := h.elemAbelian
  have hMN := h.le_normalizer
  have hYM := Y153_le Mc M
  apply le_antisymm
  · refine conjClosure_le fun m hm z hz => ?_
    have hbar : autI hV (Y153 Mc M ⊔ T) = autI hV M := h.autOn_Y153_sup_T h113
    have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hm
    have hmbar : convI hV ⟨m, hmN⟩ ∈ autI hV (Y153 Mc M ⊔ T) :=
      hbar ▸ convI_mem_autI hV hm hmN
    obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hmbar
    have hc1 : convI hV (g⁻¹ * ⟨m, hmN⟩) = 1 := by rw [map_mul, map_inv, hg, inv_mul_cancel]
    have hcC : (g : G)⁻¹ * m ∈ Subgroup.centralizer (VZ T M : Set G) :=
      (convI_eq_one_iff hV _).1 hc1
    have hzV : z ∈ VZ T M := h.Z_le_VZ hz
    have hcz : (g : G)⁻¹ * m * z * ((g : G)⁻¹ * m)⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp hcC z hzV
      calc (g : G)⁻¹ * m * z * ((g : G)⁻¹ * m)⁻¹ = ((g : G)⁻¹ * m) * z * ((g : G)⁻¹ * m)⁻¹ := rfl
        _ = z := by rw [← this]; group
    have e : m * z * m⁻¹ = (g : G) * z * (g : G)⁻¹ := by
      calc m * z * m⁻¹ = (g : G) * ((g : G)⁻¹ * m * z * ((g : G)⁻¹ * m)⁻¹) * (g : G)⁻¹ := by group
        _ = (g : G) * z * (g : G)⁻¹ := by rw [hcz]
    rw [e]
    have hTY : T ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
      h.T_le.trans (le_normalizer_Y153 Mc M)
    have hgmul := Subgroup.coe_mul_of_right_le_normalizer_left (Y153 Mc M) T hTY
    have hg' : (g : G) ∈ (Y153 Mc M : Set G) * (T : Set G) := by rw [← hgmul]; exact hgY
    obtain ⟨y, hy, t₀, ht₀, hyt⟩ := Set.mem_mul.mp hg'
    have hTz : t₀ * z * t₀⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp (h.T_le_centralizer_Z ht₀) z hz
      rw [← this]; group
    rw [← hyt]
    have e2 : y * t₀ * z * (y * t₀)⁻¹ = y * z * y⁻¹ := by
      calc y * t₀ * z * (y * t₀)⁻¹ = y * (t₀ * z * t₀⁻¹) * y⁻¹ := by group
        _ = y * z * y⁻¹ := by rw [hTz]
    rw [e2]
    exact mem_conjClosure hy hz
  · exact conjClosure_mono le_rfl hYM


theorem Y153_le_normalizer_V (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    Y153 Mc M ≤ Subgroup.normalizer (V₁ : Set G) ∧
      Y153 Mc M ≤ Subgroup.normalizer (V₂ : Set G) := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -, -⟩ := D.model
  have key : ∀ y ∈ Y153 Mc M, ∃ hyN : y ∈ Subgroup.normalizer (VZ T M : Set G),
      convI hV ⟨y, hyN⟩ ∈ L₁ ⊔ L₂ := by
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer (Y153_le Mc M hy)
    have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
    have hbar : convI hV ⟨y, hyN⟩ ∈ oTwoUpper (autI hV M) := by
      rw [← e]
      exact convI_mem_autI hV hy hyN
    exact ⟨hyN, hS.oTwoUpper_le_sup hbar⟩
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨hyN, hbar⟩ := key y hy
    exact (mem_normalizer_map_inclMod_iff hV hyN (commV L₁)).2 (hS.sup_le_stab₁ hbar)
  · obtain ⟨hyN, hbar⟩ := key y hy
    exact (mem_normalizer_map_inclMod_iff hV hyN (commV L₂)).2 (hS.sup_le_stab₂ hbar)

theorem Sgp153_le_normalizer_V₂ (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -, -⟩ := D.model
  intro s hs
  have hsN : s ∈ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer (h.T_le hs.1)
  have hbar : convI hV ⟨s, hsN⟩ ∈ autI hV (Sgp153 T ((commV L₁).map (inclMod hV))) :=
    convI_mem_autI hV hs hsN
  rw [autI_nS hV hS h.T_le] at hbar
  exact (mem_normalizer_map_inclMod_iff hV hsN (commV L₂)).2 (hS.sup_le_stab₂ hbar.2)

theorem normalizer_V_le (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) (hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M) :
    Subgroup.normalizer (V₁ : Set G) ≤ M ∧ Subgroup.normalizer (V₂ : Set G) ≤ M := by
  have hp : ∀ {V' : Subgroup G}, V' ≤ VZ T M → Nat.card V' = 4 →
      Y153 Mc M ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (V' : Set G) →
        Subgroup.normalizer (V' : Set G) ≤ M := by
    intro V' hV'V hV'4 hle
    have hp2 : IsPGroup 2 V' := (B2F.isPGroup_of_isElemAbelian h.elemAbelian).to_le hV'V
    have hbot : V' ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hV'4
      omega
    have hCO : V' ≤ pCoreOf 2 (Subgroup.normalizer (V' : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hp2
    exact le_of_isUniqueM hU ⟨hle, fun hb => hbot (le_bot_iff.mp (hb ▸ hCO))⟩
  obtain ⟨hY₁, hY₂⟩ := h.Y153_le_normalizer_V h113 D
  exact ⟨hp D.le₁ D.card₁ (sup_le hY₁ inf_le_right),
    hp D.le₂ D.card₂ (sup_le hY₂ (h.Sgp153_le_normalizer_V₂ D))⟩

theorem Yplus_ne_bot (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ≠ ⊥ := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -, -⟩ := D.model
  obtain ⟨x, hxL, hx3, hx1⟩ := exists_orderThree hS.nat₂
  have hxord : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx3 hx1
  have hxM : x ∈ autI hV M := hS.L₂_le hxL
  have hxO : x ∈ oTwoUpper (autI hV M) :=
    mem_oTwoUpper_of_odd hxM (by rw [hxord]; decide)
  have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
  have hxY : x ∈ autI hV (Y153 Mc M) := by rw [e]; exact hxO
  obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hxY
  have hgC : (g : G) ∈ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := by
    refine (mem_centralizer_map_inclMod_iff hV g.2 (commV L₁)).2 fun u hu => ?_
    have hgx : convI hV ⟨(g : G), g.2⟩ = x := hg
    rw [hgx]
    exact hS.L₂_fix₁ hxL hu
  intro hbot
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper
    (Y153 Mc M ⊓ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) (x := (g : G)) ⟨hgY, hgC⟩
  rw [hbot, Subgroup.mem_bot] at hk
  have hg1 : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hx1' : x ^ 2 ^ k = 1 := by rw [← hg, ← map_pow, hg1, map_one]
  have hdvd : 3 ∣ 2 ^ k := hxord ▸ orderOf_dvd_of_pow_eq_one hx1'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem normalizer_Yplus_le (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) (hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M) :
    Subgroup.normalizer
      (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) : Set G) ≤ M := by
  obtain ⟨hY₁, -⟩ := h.Y153_le_normalizer_V h113 D
  have hMY := le_normalizer_Y153 Mc M
  set K := Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) with hK
  have hKY : K ≤ Y153 Mc M := inf_le_left
  have hYK : Y153 Mc M ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B2F.le_normalizer_centralizer hY₁ hg⟩
  have hSK : Sgp153 T V₁ ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hMY (h.T_le hg.1), B2F.le_normalizer_centralizer (inf_le_right : Sgp153 T V₁ ≤ _) hg⟩
  have hYp := normalizer_le_normalizer_oTwoUpper K
  have hchar : CharTwo (oTwoUpper K) := by
    obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
    have hSM : (S : Subgroup G) ≤ M := hS ▸ h.T_le
    have c1 : CharTwo M := h.qtfe.qtke.2.1 M h.inM.1.1 ⟨S, hSM⟩
    have c2 : CharTwo (Y153 Mc M) :=
      A4.charTwo_of_normal (Y153_le Mc M) (le_normalizer_Y153 Mc M) c1
    have c3 : CharTwo K := A4.charTwo_of_normal hKY hYK c2
    exact A4.charTwo_of_normal (oTwoUpper_le K) (le_normalizer_oTwoUpper K) c3
  have hO : pCoreOf 2 (oTwoUpper K) ≠ ⊥ := by
    intro hb
    apply h.Yplus_ne_bot h113 D
    have h1 : oTwoUpper K ⊓ Subgroup.centralizer (pCoreOf 2 (oTwoUpper K) : Set G) ≤
        pCoreOf 2 (oTwoUpper K) := hchar
    rw [hb] at h1
    show oTwoUpper K = ⊥
    rw [eq_bot_iff]
    intro x hx
    exact h1 ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [show (y : G) = 1 from by simpa using hy, mul_one, one_mul]⟩
  have hle : Y153 Mc M ⊔ Sgp153 T V₁ ≤
      Subgroup.normalizer (pCoreOf 2 (oTwoUpper K) : Set G) :=
    sup_le ((hYK.trans hYp).trans (normalizer_le_normalizer_pCoreOf 2 _))
      ((hSK.trans hYp).trans (normalizer_le_normalizer_pCoreOf 2 _))
  have hCO : pCoreOf 2 (oTwoUpper K) ≤
      pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 (oTwoUpper K) : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl (pCoreOf_isPGroup 2 _)
  have hH : InH (Y153 Mc M ⊔ Sgp153 T V₁)
      (Subgroup.normalizer (pCoreOf 2 (oTwoUpper K) : Set G)) :=
    ⟨hle, fun hb => hO (le_bot_iff.mp (hb ▸ hCO))⟩
  exact (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper K)).trans (le_of_isUniqueM hU hH)

end Hyp153

namespace Hyp15310

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem lemma_15_3_11_four_case_one (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hY : Yp = Y153 Mc M) {I : Subgroup G} :
    I ⊓ Subgroup.normalizer (Yp : Set G) = M ⊓ I := by
  rw [hY, ← h.hyp.lemma_15_3_7_normalizer h113, inf_comm]

theorem lemma_15_3_11_two_case_one (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hY : Yp = Y153 Mc M) {I : Subgroup G}
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    I ⊓ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) I : Set G) ≤ M ⊓ I := by
  have hYI : Y153 Mc M ≤ I := hY ▸ (le_sup_left.trans hI.1.1)
  have hVU : VZ T M ≤ conjClosure (quasithinOmegaOneCenter T) I := by
    rw [h.hyp.VZ_eq_conjClosure_Y153 h113]
    exact conjClosure_mono le_rfl hYI
  intro x hx
  refine ⟨?_, hx.1⟩
  have hxV : x ∈ Subgroup.centralizer (VZ T M : Set G) := Subgroup.centralizer_le hVU hx.2
  have hHv : M = Subgroup.normalizer (VZ T M : Set G) := h.hyp.isHv_of_inM' h.hyp.inM
  rw [hHv]
  exact Subgroup.centralizer_le_normalizer _ hxV

end Hyp15310

end CFSG.Quasithin
