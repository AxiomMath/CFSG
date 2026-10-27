module

public import CFSG.Quasithin.EmptyFaithful.S153SwapCentralizer
public import CFSG.Quasithin.EmptyFaithful.S153D56
public import CFSG.Quasithin.MS93.ASC134Sq
public import CFSG.Quasithin.EmptyFaithful.SzC4S8DMain
public import CFSG.Quasithin.Vol2.Ch4Sec3Setup
public import CFSG.Quasithin.EmptyFaithful.S153H31
public import CFSG.Quasithin.EmptyFaithful.SBc11Case45
public import CFSG.Quasithin.EmptyFaithful.SBc11Hat
public import CFSG.Quasithin.EmptyFaithful.SzN3Lin2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SBc11
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem Y153_eq_sup_centralizers_of_swap (h113 : StageLemma14113)
    {T Mc M V₁ V₂ Yp : Subgroup G} {t t₁ : G} (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (htT : t₁ ∈ T) (htS : t₁ ∉ Sgp153 T V₁) :
    Y153 Mc M = (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔
      (Y153 Mc M ⊓ Subgroup.centralizer (V₂ : Set G)) := by
  set Y : Subgroup G := Y153 Mc M with hY
  set K₁ : Subgroup G := Y ⊓ Subgroup.centralizer (V₁ : Set G) with hK₁
  set K₂ : Subgroup G := Y ⊓ Subgroup.centralizer (V₂ : Set G) with hK₂
  set K₀ : Subgroup G := Y ⊓ Subgroup.centralizer (VZ T M : Set G) with hK₀
  have hD := h.decomp
  have hYV := h.hyp.Y153_le_normalizer_V h113 hD
  have hYN : Y ≤ Subgroup.normalizer (Y : Set G) := fun y hy =>
    le_normalizer_Y153 Mc M (Y153_le Mc M hy)
  have hK₁N : Y ≤ Subgroup.normalizer (K₁ : Set G) := fun y hy =>
    A4.mem_normalizer_of_conj_mem fun x hx =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hYN hy) x).mp hx.1,
        S153D.conj_mem_centralizer (hYV.1 hy) hx.2⟩
  have hK₂N : Y ≤ Subgroup.normalizer (K₂ : Set G) := fun y hy =>
    A4.mem_normalizer_of_conj_mem fun x hx =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hYN hy) x).mp hx.1,
        S153D.conj_mem_centralizer (hYV.2 hy) hx.2⟩
  have hK₂N₁ : K₂ ≤ Subgroup.normalizer (K₁ : Set G) :=
    fun x hx => hK₁N ((inf_le_left : K₂ ≤ Y) hx)
  have hV₁eq : B6.conjSub t₁ V₁ = V₂ :=
    (szN3_conj_V_swap h.hyp hD htT htS).1
  have hYt : B6.conjSub t₁ Y = Y :=
    B6.conjSub_eq_self (le_normalizer_Y153 Mc M (h.hyp.T_le htT))
  have hK₂eq : B6.conjSub t₁ K₁ = K₂ := by
    rw [hK₁, hK₂, hY]
    rw [OrderIso.map_inf, hYt, szN3_conjSub_centralizer, hV₁eq]
  have hinf : K₁ ⊓ K₂ = K₀ := by
    rw [hK₁, hK₂, hK₀, hY]
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx1.1, ?_⟩
      have hz1 : V₁ ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
        Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hx1.2)
      have hz2 : V₂ ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
        Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hx2.2)
      have hz : V₁ ⊔ V₂ ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := sup_le hz1 hz2
      have hxC : x ∈ Subgroup.centralizer (((V₁ ⊔ V₂ : Subgroup G)) : Set G) :=
        Subgroup.zpowers_le.mp (Subgroup.le_centralizer_iff.mpr hz)
      rw [hD.sup] at hxC
      exact hxC
    · rintro ⟨hxY, hx⟩
      have hV₁VZ : V₁ ≤ VZ T M := by rw [← hD.sup]; exact le_sup_left
      have hV₂VZ : V₂ ≤ VZ T M := by rw [← hD.sup]; exact le_sup_right
      exact ⟨⟨hxY, Subgroup.centralizer_le hV₁VZ hx⟩, hxY,
        Subgroup.centralizer_le hV₂VZ hx⟩
  have hcardK₁ : Nat.card K₁ = 3 * Nat.card K₀ := by
    rw [hK₁, hK₀, hY]
    exact Hyp153.card_Yplus_base h113 h.hyp hD
  have hcardK₂ : Nat.card K₂ = Nat.card K₁ := by
    rw [← hK₂eq]
    exact Nat.card_congr (Subgroup.equivMapOfInjective K₁ (MulAut.conj t₁).toMonoidHom
      (MulAut.conj t₁).injective).toEquiv.symm
  have hcard_sup : Nat.card ↥(K₁ ⊔ K₂) * Nat.card K₀ = Nat.card K₁ * Nat.card K₂ := by
    have h := CFSG.Quasithin.H13.Ch4.card_sup_mul_card_inf_of_le_normalizer
      (L := K₁) (X := K₂) hK₂N₁
    rwa [hinf] at h
  have hcardP : Nat.card ↥(K₁ ⊔ K₂) = 9 * Nat.card K₀ := by
    have h := hcard_sup
    rw [hcardK₁, hcardK₂, hcardK₁] at h
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥K₀)) ?_
    calc Nat.card ↥(K₁ ⊔ K₂) * Nat.card K₀ = (3 * Nat.card K₀) * (3 * Nat.card K₀) := h
      _ = (9 * Nat.card K₀) * Nat.card K₀ := by ring
  have hcardY : Nat.card Y = 9 * Nat.card K₀ := by
    rw [hY, hK₀]
    exact Hyp153.card_Y153 h113 h.hyp
  have hle : K₁ ⊔ K₂ ≤ Y := sup_le inf_le_left inf_le_left
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP, hcardY])).symm

private theorem Y153_le_sup_oTwoUpper_centralizers (h113 : StageLemma14113)
    {T Mc M V₁ V₂ Yp : Subgroup G} {t : G} (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    Y153 Mc M ≤ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔
      oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₂ : Set G)) := by
  set Y : Subgroup G := Y153 Mc M with hY
  set K₁ : Subgroup G := Y ⊓ Subgroup.centralizer (V₁ : Set G) with hK₁
  set K₂ : Subgroup G := Y ⊓ Subgroup.centralizer (V₂ : Set G) with hK₂
  set O : Subgroup G := pCoreOf 2 Y with hO
  set Yp1 : Subgroup G := oTwoUpper K₁ with hYp1
  set Yp2 : Subgroup G := oTwoUpper K₂ with hYp2
  set P : Subgroup G := Yp1 ⊔ Yp2 with hP
  obtain ⟨t₁, htT, htS, hconj⟩ :=
    szN3_exists_swap h.hyp h.decomp (YL := Yp1) (YC := Yp2) (Or.inl ⟨rfl, rfl⟩)
  have hYeq : Y = K₁ ⊔ K₂ := Y153_eq_sup_centralizers_of_swap h113 h htT htS
  have hK₁le : K₁ ≤ Yp1 ⊔ O := by
    rw [hK₁, hYp1, hO, hY]
    exact Hyp153.Yplus_base_le h113 h.hyp
  have htY : t₁ ∈ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_Y153 Mc M (h.hyp.T_le htT)
  have htO : t₁ ∈ Subgroup.normalizer (O : Set G) := by
    rw [hO]; exact normalizer_le_normalizer_pCoreOf 2 Y htY
  have hOeq : B6.conjSub t₁ O = O := B6.conjSub_eq_self htO
  have hK₂eq : B6.conjSub t₁ K₁ = K₂ := by
    rw [hK₁, hK₂, hY]
    rw [OrderIso.map_inf, B6.conjSub_eq_self htY, szN3_conjSub_centralizer,
      (szN3_conj_V_swap h.hyp h.decomp htT htS).1]
  have hK₂le : K₂ ≤ Yp2 ⊔ O := by
    have hmap : B6.conjSub t₁ (Yp1 ⊔ O) = Yp2 ⊔ O := by
      rw [OrderIso.map_sup, hconj, hOeq]
    calc K₂ = B6.conjSub t₁ K₁ := hK₂eq.symm
      _ ≤ B6.conjSub t₁ (Yp1 ⊔ O) := (B6.conjSub t₁).le_iff_le.mpr hK₁le
      _ = Yp2 ⊔ O := hmap
  have hYN : Y ≤ Subgroup.normalizer (Y : Set G) := fun y hy =>
    le_normalizer_Y153 Mc M (Y153_le Mc M hy)
  have hYV := h.hyp.Y153_le_normalizer_V h113 h.decomp
  have hK₁N : Y ≤ Subgroup.normalizer (K₁ : Set G) := fun y hy =>
    A4.mem_normalizer_of_conj_mem fun x hx =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hYN hy) x).mp hx.1,
        S153D.conj_mem_centralizer (hYV.1 hy) hx.2⟩
  have hK₂N : Y ≤ Subgroup.normalizer (K₂ : Set G) := fun y hy =>
    A4.mem_normalizer_of_conj_mem fun x hx =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hYN hy) x).mp hx.1,
        S153D.conj_mem_centralizer (hYV.2 hy) hx.2⟩
  have hYp1N : Y ≤ Subgroup.normalizer (Yp1 : Set G) := by
    rw [hYp1]
    exact hK₁N.trans (normalizer_le_normalizer_oTwoUpper K₁)
  have hYp2N : Y ≤ Subgroup.normalizer (Yp2 : Set G) := by
    rw [hYp2]
    exact hK₂N.trans (normalizer_le_normalizer_oTwoUpper K₂)
  have hPn : Y ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP]
    exact fun y hy => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hYp1N hy, hYp2N hy⟩
  have hPY : P ≤ Y := by
    rw [hP]
    exact sup_le ((oTwoUpper_le K₁).trans inf_le_left) ((oTwoUpper_le K₂).trans inf_le_left)
  have hYPO : Y = P ⊔ O := by
    apply le_antisymm ?_ (sup_le hPY (pCoreOf_le 2 Y))
    have h1 : Yp1 ⊔ O ≤ P ⊔ O := by
      rw [hP]
      refine sup_le ?_ ?_
      · exact le_trans (le_sup_left : Yp1 ≤ Yp1 ⊔ Yp2)
          (le_sup_left : Yp1 ⊔ Yp2 ≤ (Yp1 ⊔ Yp2) ⊔ O)
      · exact le_sup_right
    have h2 : Yp2 ⊔ O ≤ P ⊔ O := by
      rw [hP]
      refine sup_le ?_ ?_
      · exact le_trans (le_sup_right : Yp2 ≤ Yp1 ⊔ Yp2)
          (le_sup_left : Yp1 ⊔ Yp2 ≤ (Yp1 ⊔ Yp2) ⊔ O)
      · exact le_sup_right
    have hKC : K₁ ⊔ K₂ ≤ (Yp1 ⊔ O) ⊔ (Yp2 ⊔ O) :=
      sup_le (hK₁le.trans le_sup_left) (hK₂le.trans le_sup_right)
    have hle : (Yp1 ⊔ O) ⊔ (Yp2 ⊔ O) ≤ P ⊔ O := sup_le h1 h2
    exact (le_of_eq hYeq).trans (hKC.trans hle)
  have hO2 : IsPGroup 2 O := by rw [hO]; exact pCoreOf_isPGroup 2 Y
  have hpowmem : ∀ y ∈ Y, ∃ j : ℕ, y ^ 2 ^ j ∈ P := by
    intro y hy
    have hy' : y ∈ (P ⊔ O : Subgroup G) := hYPO ▸ hy
    have hOP : O ≤ Subgroup.normalizer (P : Set G) := fun o ho => hPn ((pCoreOf_le 2 Y) ho)
    obtain ⟨p, hp, o, ho, hpo⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes (H := P) (K := O) hOP).mp hy'
    obtain ⟨k, hk⟩ := hO2 ⟨o, ho⟩
    have hk' : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hoY : o ∈ Y := (pCoreOf_le 2 Y) ho
    obtain ⟨p', hp', hpow⟩ := A4.exists_pow_mul_eq (H := P) hp (hPn hoY) (2 ^ k)
    refine ⟨k, ?_⟩
    rw [hpo, hpow, hk', mul_one]
    exact hp'
  have hYleP : Y ≤ P := by
    have h := oTwoUpper_le_of_pow_mem (X := Y) (N := P) hpowmem
    have hYid : oTwoUpper Y = Y := by
      rw [hY]
      exact oTwoUpper_oTwoUpper _
    rwa [hYid] at h
  exact hYleP

private theorem Y153_le_sup_conjSub (h113 : StageLemma14113)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    ∃ t₁ ∈ T, t₁ ∉ Sgp153 T V₁ ∧ Y153 Mc M ≤ L ⊔ B6.conjSub t₁ L := by
  set Y : Subgroup G := Y153 Mc M with hY
  set Yp1 : Subgroup G := oTwoUpper (Y ⊓ Subgroup.centralizer (V₁ : Set G)) with hYp1
  set Yp2 : Subgroup G := oTwoUpper (Y ⊓ Subgroup.centralizer (V₂ : Set G)) with hYp2
  have h2 := Hyp15310.case_two_of_pRank_one h113 c.ctx.hyp c.ctx.rank
  have hYp : Yp = Yp1 := h2.2
  obtain ⟨t₁, htT, htS, hconj⟩ :=
    szN3_exists_swap c.ctx.hyp.hyp c.ctx.hyp.decomp (YL := Yp1) (YC := Yp2)
      (Or.inl ⟨rfl, rfl⟩)
  refine ⟨t₁, htT, htS, ?_⟩
  have hYp1L : Yp1 ≤ L := by rw [← hYp]; exact c.c27.Yp_le
  have hYp2L : Yp2 ≤ B6.conjSub t₁ L :=
    hconj ▸ (B6.conjSub t₁).le_iff_le.mpr hYp1L
  have hYle : Y ≤ Yp1 ⊔ Yp2 := by
    rw [hY]
    exact Y153_le_sup_oTwoUpper_centralizers h113 c.ctx.hyp
  have hPle : Yp1 ⊔ Yp2 ≤ L ⊔ B6.conjSub t₁ L :=
    sup_le (hYp1L.trans le_sup_left) (hYp2L.trans le_sup_right)
  exact hYle.trans hPle

theorem c134SqCond_of_ctx15331 (h113 : StageLemma14113)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    MS93.C134SqCond (Sgp153 T V₁) L := by
  intro T₁ hT₁S hchar
  set S : Subgroup G := Sgp153 T V₁ with hS
  obtain ⟨t₁, htT, htS₀, hYLE⟩ := Y153_le_sup_conjSub h113 c
  have htS : t₁ ∉ S := by rw [hS]; exact htS₀
  have hTS : T ≤ Subgroup.normalizer (S : Set G) := by
    rw [hS]
    exact Hyp153.T_le_normalizer_Sgp153 c.ctx.hyp.hyp c.ctx.hyp.decomp
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := by
    have hSI : S ≤ I := by
      rw [hS, c.I_eq]
      exact le_sup_right
    exact hSI.trans c.c27.normal
  have hLM : ¬ L ≤ M := fun hLM =>
    c.conc.2.1 (le_inf hLM (S153H.le_I_of_ctx31 c))
  have hidx : (S.subgroupOf T).index = 2 := by
    rw [hS]
    exact c.ctx.hyp.decomp.relIndex_nS c.ctx.hyp.hyp
  have hT : ∀ g ∈ T, g ∈ S ∨ t₁⁻¹ * g ∈ S := by
    intro g hg
    by_cases hgS : g ∈ S
    · exact Or.inl hgS
    · right
      have hmem : (⟨t₁⁻¹, T.inv_mem htT⟩ : T) * ⟨g, hg⟩ ∈ S.subgroupOf T :=
        (Subgroup.mul_mem_iff_of_index_two hidx).2
          (iff_of_false (fun h => htS (by simpa using S.inv_mem (Subgroup.mem_subgroupOf.mp h))) hgS)
      exact Subgroup.mem_subgroupOf.mp hmem
  have ht2 : t₁ * t₁ ∈ S := by
    have hmem : (⟨t₁, htT⟩ : T) * ⟨t₁, htT⟩ ∈ S.subgroupOf T :=
      (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false htS htS)
    exact Subgroup.mem_subgroupOf.mp hmem
  have hA : IsPGroup 2 ↥(omegaOneCenterOf T₁) :=
    B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_omegaOneCenterOf T₁)
  have hTA : T ≤ Subgroup.normalizer (omegaOneCenterOf T₁ : Set G) :=
    (hTS.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hT₁S hchar)).trans
      (normalizer_le_normalizer_omegaOneCenterOf T₁)
  exact card_inf_centralizer_sq_le (X := Y153 Mc M ⊔ S) (M := M) (Y := Y153 Mc M)
    (T := T) (S := S) (L := L) (A := omegaOneCenterOf T₁) (t := t₁)
    (Hyp15310.case_two_of_pRank_one h113 c.ctx.hyp c.ctx.rank).1
    (sup_le_sup_left inf_le_left (Y153 Mc M)) hYLE hLM htT hT ht2 hSL hTS hA hTA

theorem input31MSOutcome_of_c132_sq (h113 : StageLemma14113) (hC132 : ASInputs.AS_C_1_32)
    (hC134 : MS93.MRes.AS_C_1_34_corrWOneSq) : Input31MSOutcome := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hlist _
  have hMS := isMSPair_of_ctx c hlist
  have hLc : L ∈ cComp I := (ctx_basic c).1
  have hset := coe_eq_mul_of_ctx c
  unfold Outcome31
  rcases hC132 G I (Sgp153 T V₁) L hMS hLc hset with
    hg2 | halt | hsp4 | hhat | ⟨n, F, hF, hFin, α, hcard, hmod⟩
  · exact ⟨Or.inr (Or.inl hg2), centralizer_UI_eq_pCoreOf_of_g2Block c hg2⟩
  · exact ⟨Or.inl halt, centralizer_UI_eq_pCoreOf_of_altBlock c halt⟩
  · exact (not_isSp4Block c hlist hsp4).elim
  · exact (not_isHatA6Block c hlist hhat).elim
  · obtain ⟨hn, hpsl⟩ := sl3_case c hlist hcard hmod
    subst hn
    have hF2 : Fintype.card F = 2 := by simpa using hcard
    refine ⟨Or.inr (Or.inr ⟨hpsl, ?_⟩), sl3_centralizer c hlist hF2 hmod⟩
    obtain ⟨i, hi⟩ := hC134 G I (Sgp153 T V₁) L hMS hLc hset
      ⟨F, hF, hFin, α, hF2, hmod⟩ (c134SqCond_of_ctx15331 h113 c)
    match i, hi with
    | 0, h => exact False.elim h
    | 1, h => exact Or.inl h
    | 2, h => exact Or.inr (Or.inl h)
    | 3, h => exact Or.inr (Or.inr h)
    | 4, h => exact (s8_case4_false_of_rigidAt h113 c hlist h.1 fun hn1 =>
        c134Case4RigidAt_of_zq2 hset h.1 hn1 (zq2_of_abW h.1 hn1 h.2)).elim
    | 5, h => exact (not_isC134Case5 h113 c h).elim
    | _ + 6, h => exact False.elim h

end CFSG.Quasithin.SzC4
