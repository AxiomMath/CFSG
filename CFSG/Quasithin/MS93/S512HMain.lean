module

public import CFSG.Quasithin.MS93.S512HStep
public import CFSG.Quasithin.MS93.S512FStar
public import CFSG.Quasithin.MS93.S512FAlt
public import CFSG.Quasithin.MS93.S512HMod
public import CFSG.Quasithin.MS93.S512RLem
public import CFSG.Quasithin.MS93.S512RPair

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512H

theorem le_normalizer_commutator_sup {Γ : Type*} [Group Γ] {Z Y X Q R : Subgroup Γ}
    (hZY : Z ≤ Subgroup.normalizer ((Y ⊔ X : Subgroup Γ) : Set Γ))
    (hZQ : Z ≤ Subgroup.normalizer (Q : Set Γ)) (hYX : Y ≤ Subgroup.normalizer (X : Set Γ))
    (hXQ : X ≤ Subgroup.centralizer (Q : Set Γ)) (hZR : Z ≤ Subgroup.centralizer (R : Set Γ)) :
    Z ≤ Subgroup.normalizer ((⁅Y, Q⁆ ⊔ R : Subgroup Γ) : Set Γ) := by
  refine le_normalizer_sup ?_ (hZR.trans (Subgroup.centralizer_le_normalizer _))
  refine le_normalizer_of_map_conj_le fun z hz => ?_
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hZQ hz)]
  refine (Subgroup.commutator_mono ?_ le_rfl).trans (commutator_sup_le_left hYX hXQ)
  calc Y.map (MulAut.conj z).toMonoidHom ≤ (Y ⊔ X).map (MulAut.conj z).toMonoidHom :=
        Subgroup.map_mono le_sup_left
    _ = Y ⊔ X := map_conj_eq_of_mem_normalizer (hZY hz)

theorem le_normalizer_iInf_map_conj {Γ : Type*} [Group Γ] (H K : Subgroup Γ) :
    H ≤ Subgroup.normalizer
      ((⨅ t : ↥H, K.map (MulAut.conj (t : Γ)).toMonoidHom : Subgroup Γ) : Set Γ) := by
  refine le_normalizer_of_map_conj_le fun s hs => ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_iInf] at hx
  rw [Subgroup.mem_iInf]
  intro t
  have h1 := hx ⟨s⁻¹ * t, H.mul_mem (H.inv_mem hs) t.2⟩
  rw [mem_map_conj] at h1 ⊢
  simpa [mul_assoc] using h1

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem false_of_threeAlt2 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (h58 : S5B.S58) (hq2 : S5B.Q2Cent) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)} (hch : S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂)
    (hq1 : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    (hq : (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k)
    (h56 : ∀ l : Submodule F (MSP.V4 F),
      ¬ S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    (hline : ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
      Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) ∧
      S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _))
    (hc55 : S5.Concl55 h (2 ^ k) α' (geo _ (baseA (puAmalgam h.le)) α' 2) g x)
    (hμeq : μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
      μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
    (hL : ¬ puTrans h.le L (baseA _) ≤
      S5.jOff h.le L (2 ^ k) μ₁ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ⊔
        S5.zHat _ (baseA _) α')
    (hTY : ¬ Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ≤ Subgroup.normalizer
      ((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) : Subgroup _) :
        Set (puAmalgam h.le).Universal))
    (hlarge : 2 ^ k < (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L μ₁)) : False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hk1 : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hst := S5.ofA_range_eq (hTM := h.le)
  obtain ⟨hc, hαβ, hcμ, -, hdμ, hmid, -⟩ := S512T.chain_geo h hb4 hch
  obtain ⟨hμM, hγM, -, -, hμρ, hρα, -, -, -, hαγ, -, -⟩ := S512T.pair_facts h hb4 hcμ
  rw [hmid] at hρα hαγ
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  set ρ := geo _ μ₁ γ 1 with hρdef
  set U := S5.uSub h.le L μ₁ with hUdef
  set R₂ := ⁅U, ZM _ γ⁆ with hR₂def
  set Y := U ⊓ Qv _ γ with hYdef
  have hρ : ¬ IsMVtx _ ρ := (isMVtx_iff_of_adj _ hμρ).1 hμM
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  obtain ⟨ρ', hαρ', hρ'μ, hgen⟩ := S512F.exists_qv_sup_zm_eq_stab' h hd hc hαβ hq1 hg hx hc55 hμeq
  rw [S512T.eq_geo_one_of_adj h hb4 hcμ hmid hαρ' hρ'μ] at hgen
  have hZh := S512T.zHat_eq h hd hc hq1
  obtain ⟨p₁, hp₁, hZp⟩ : ∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧
      S5.vIm h.le a (ZM _ α') = MSP.xPoint p := by
    rcases S33.shape_of_sp4Data h hd hc with ⟨-, -, hp⟩ | ⟨h1, -, -⟩
    · exact hp
    · exfalso
      rw [hq1] at h1
      have : 2 ^ k < (2 ^ k) ^ 2 := by nlinarith
      omega
  have hTρα : Qv _ ρ ≤ stab _ (baseA (puAmalgam h.le)) := qv_le_stab_of_adj _ hρα
  have hTμ : Qv _ ρ ≤ stab _ μ₁ := qv_le_stab_of_adj _ hμρ.symm
  have hZst : ZM _ α' ≤ stab _ (baseA (puAmalgam h.le)) := (S5B.crit_facts h hc).1
  have hQμρ : Qv _ μ₁ ≤ Qv _ ρ := qv_le_qv _ hyp hμM hμρ
  have hQαρ : Qv _ (baseA (puAmalgam h.le)) ≤ Qv _ ρ := qv_le_qv _ hyp hα hρα.symm
  have hQαμ : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ μ₁ := hQαρ.trans hTμ
  have hT2 : IsPGroup 2 (Qv (puAmalgam h.le) ρ) := isPGroup_qv _ hyp hρ
  have hUn : stab _ μ₁ ≤ Subgroup.normalizer (U : Set (puAmalgam h.le).Universal) :=
    S5B.stab_le_normalizer_uSub_at h μ₁
  have hUZ : U ≤ ZM _ μ₁ := S5B.uSub_le_zm h.le μ₁
  have hUQα : U ≤ Qv _ (baseA (puAmalgam h.le)) :=
    hUZ.trans (zm_le_qv_of_dist_lt _ hμM (by rw [SimpleGraph.dist_comm]; omega))
  have hUQμ : U ≤ Subgroup.centralizer (Qv _ μ₁ : Set (puAmalgam h.le).Universal) :=
    hUZ.trans (zm_le_centralizer_qv _ hyp hμM)
  have hZγα : ZM _ γ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ hγM (by rw [SimpleGraph.dist_comm, hαγ]; omega)
  have hZγμ : ZM _ γ ≤ stab _ μ₁ := hZγα.trans hQαμ
  have hXαQ : XM _ (baseA (puAmalgam h.le)) ≤
      Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) :=
    Subgroup.le_centralizer_iff.1 (qv_le_centralizer_xm _ _)
  have hRU : R₂ ≤ U :=
    commutator_le_left_of_le_normalizer (hZγμ.trans hUn)
  have hRZ : R₂ ≤ ZM _ γ := (S512T.commutator_uSub_zm_le h hb4 hcμ).trans inf_le_left
  have hRX : R₂ ≤ XM _ (baseA (puAmalgam h.le)) := by
    have hV1 : U ≤ Vv _ (baseA (puAmalgam h.le)) := hUZ.trans (S5B.zm_le_vv_of_dist hμM hdμ.le)
    have hV2 : ZM _ γ ≤ Vv _ (baseA (puAmalgam h.le)) := S5B.zm_le_vv_of_dist hγM hαγ.le
    exact (Subgroup.commutator_mono hV1 hV2).trans
      (h52 G M T L h hmin hb k F _ _ a hd α' hc).2.2.1
  have hZα'R : ZM _ α' ≤ Subgroup.centralizer (R₂ : Set (puAmalgam h.le).Universal) := by
    have h1 : ZM _ γ ≤ Qv _ α' := zm_le_qv_of_dist_lt _ hγM (by
      rw [dist_geo_right _ (by omega), hd4]; omega)
    exact (zm_le_centralizer_qv _ hyp (hc.isMVtx_right _ hyp)).trans
      (Subgroup.centralizer_le (hRZ.trans h1))
  obtain ⟨l, hl, -, hJl⟩ := hline
  have hQJ := S512F.qv_le_jOff_of_not_le h hb4 hch hg hx hc55 hμeq hL
  have hUX := S512F.commutator_uSub_qv_le_xm h hb hd hl hJl hμM hρα.symm hμρ.symm hQJ
  have hQne : MSP.fixSp (S5.vIm h.le a (Qv _ μ₁)) ≠ ⊤ := by
    intro htop
    have hQμα : Qv _ μ₁ ≤ stab _ (baseA (puAmalgam h.le)) := hQμρ.trans hTρα
    have hbot : S5.vIm h.le a (Qv _ μ₁) = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      rw [Subgroup.mem_bot]
      refine MSP.ext_mulVec fun v => ?_
      have hv : v ∈ MSP.fixSp (S5.vIm h.le a (Qv _ μ₁)) := by rw [htop]; exact Submodule.mem_top
      rw [MSP.mem_fixSp.1 hv e he, MSP.mat_one, Matrix.one_mulVec]
    have h1 := S33.relIndex_qv_baseA_eq_card h hd hQμα (hT2.to_le hQμρ)
    rw [hbot, Subgroup.card_bot, Subgroup.relIndex_eq_one] at h1
    have : Finite ↥(Qv _ (baseA (puAmalgam h.le))) := by
      rw [S5B.qv_baseA_eq h]
      exact S5B.finite_imM h.le _
    have h2 : Qv _ μ₁ = Qv _ (baseA (puAmalgam h.le)) :=
      Subgroup.eq_of_le_of_card_ge h1 (S5B.card_qv_eq h hμM).ge
    have h3 : U ≤ Subgroup.centralizer
        (Qv _ (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) := h2 ▸ hUQμ
    rw [Subgroup.relIndex_eq_one.2 h3] at hlarge
    omega
  have hTQ : Qv _ ρ ≤ Subgroup.normalizer (Qv _ μ₁ : Set (puAmalgam h.le).Universal) :=
    hTμ.trans (stab_le_normalizer_qv _ _)
  have hpQ := point_inf_fixSp_eq_bot h hd hTρα hZst hgen hTQ hp₁ hZp hQne
  have hone : ZM _ α' ≤ Subgroup.normalizer ((Y ⊔ XM _ (baseA (puAmalgam h.le)) :
      Subgroup _) : Set (puAmalgam h.le).Universal) := by
    obtain ⟨-, hs0, hgeo, -, hμlam, -, -⟩ := hch
    have hmem : baseA _ ∈ S5B.lamAllAt h (2 ^ k) a γ ν :=
      S5B.mem_lamAllAt_of_mem_lamAt h hs0.1 hs0.2.1
        (S5B.not_uSub_le_bSub_of_isCritical h58 h hmin hb hd hs0.1)
    have := S5B.s512One_case55 h32 hX2 h52 h54 h hmin hb4 hd hc hαβ hs0.1 hgeo hmem h56 hμlam
    rwa [hZh] at this
  set X := ⁅Y, Qv _ (baseA (puAmalgam h.le))⁆ ⊔ R₂ with hXdef
  have hYQα : Y ≤ Qv _ (baseA (puAmalgam h.le)) := inf_le_left.trans hUQα
  have hZX : ZM _ α' ≤ Subgroup.normalizer (X : Set (puAmalgam h.le).Universal) :=
    le_normalizer_commutator_sup hone (hZst.trans (stab_le_normalizer_qv _ _))
      (hYQα.trans ((qv_le_stab _ _).trans (stab_le_normalizer_xm _ _))) hXαQ hZα'R
  have hYQU : ⁅Y, Qv _ (baseA (puAmalgam h.le))⁆ ≤ ⁅U, Qv _ (baseA (puAmalgam h.le))⁆ :=
    Subgroup.commutator_mono inf_le_left le_rfl
  have hXU : X ≤ U :=
    sup_le (hYQU.trans (commutator_le_left_of_le_normalizer (hQαμ.trans hUn))) hRU
  have hXX : X ≤ XM _ (baseA (puAmalgam h.le)) := sup_le (hYQU.trans hUX) hRX
  set Xh := imM h.le (S5Q2.X52.xFix h) with hXhdef
  have hXhn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (Xh : Set (puAmalgam h.le).Universal) := by
    rw [puAmalgam.stab_baseA]
    exact S5B.imM_le_normalizer h.le (le_normalizer_xFix h)
  set X' := X ⊓ Xh with hX'def
  have hZX' : ZM _ α' ≤ Subgroup.normalizer (X' : Set (puAmalgam h.le).Universal) :=
    (le_inf hZX (hZst.trans hXhn)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hZc := S5B.zq_le_centralizer hq2 h hmin hb hd
  have hcommX : ∀ s ∈ X', ∀ z ∈ ZM _ α', ⁅z, s⁆ ∈ imM h.le (Zq M L) := by
    intro s hs z hz
    have hzs : ⁅z, s⁆ ∈ X := by
      have h1 : z * s * z⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hZX hz) s).1 hs.1
      rw [commutatorElement_def]
      exact X.mul_mem h1 (X.inv_mem hs.1)
    exact commutator_mem_zq_baseA h hd hZc hZst (hQμρ.trans hTρα) hp₁ hZp.le hpQ hs.2 hz
      (hXU.trans hUQμ hzs)
  have hRXh : R₂ ≤ Xh := by
    have hp0 : p₁ ≠ ⊥ := by
      intro hp0
      have h1 : Module.finrank F p₁ = 1 := hp₁
      rw [hp0, finrank_bot] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨v, hvp, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
    have hpv : F ∙ v = p₁ := Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem v p₁).2 hvp)
      (by rw [finrank_span_singleton hv0]; exact (show Module.finrank F p₁ = 1 from hp₁).symm)
    have htv : MSP.transv v 1 ∈ S5.vIm h.le a (ZM _ α') := by
      rw [hZp, ← hpv]
      exact MSP.transv_mem_xPoint v 1
    obtain ⟨z₀, hz₀, hz₀a⟩ := htv
    have hz₀n : k = 1 → a z₀ ∉ commutator (StatedSp 2 F) := fun hk => by
      rw [hz₀a]
      exact MSP.transv_not_mem_commutator_of_card_two (by rw [hd.nat_card_eq, hk]; rfl) hv0 1
        one_ne_zero
    rw [S5B.xm_baseA_eq h] at hRX
    intro r hr
    obtain ⟨r₀, hr₀, rfl⟩ := hRX hr
    have hc₀ : (z₀ : G) * r₀ = r₀ * z₀ := by
      have h1 := Subgroup.mem_centralizer_iff.1 (hZα'R hz₀) _ hr
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1).symm
    exact ⟨r₀, Subgroup.mem_subgroupOf.2 (mem_xFix_of_commute h hd (h32 G M T L h).2.1
      (Subgroup.mem_subgroupOf.1 hr₀) z₀.2 hz₀n hc₀), rfl⟩
  have hYc : Y = U ⊓ Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal) :=
    S512T.uSub_inf_qv_eq h hb4 hcμ
  have hrelE : (Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal)).relIndex U =
      2 ^ k := by
    rw [← S512T.relIndex_qv_zm_eq h hb4 hcμ]
    exact hq
  have hR₂t : ∀ t ∈ Qv _ ρ, R₂.map (MulAut.conj t).toMonoidHom ≤ X := by
    intro t ht
    have htμ : t ∈ stab _ μ₁ := hTμ ht
    have htα : t ∈ stab _ (baseA (puAmalgam h.le)) := hTρα ht
    have hUt : U.map (MulAut.conj t).toMonoidHom = U := by
      rw [hUdef, ← S5B.uSub_smul h.le hLn, (mem_stab _).1 htμ]
    set E' := (ZM _ γ).map (MulAut.conj t).toMonoidHom with hE'
    have hE'μ : E' ≤ stab _ μ₁ := by
      have := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hZγμ
      rwa [← stab_smul, (mem_stab _).1 htμ] at this
    have hE'α : E' ≤ Qv _ (baseA (puAmalgam h.le)) := by
      have := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hZγα
      rwa [← qv_smul, (mem_stab _).1 htα] at this
    have hRt : R₂.map (MulAut.conj t).toMonoidHom = ⁅U, E'⁆ := by
      rw [hR₂def, Subgroup.map_commutator, hUt]
    have hYt : (U ⊓ Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal)).map
        (MulAut.conj t).toMonoidHom = U ⊓ Subgroup.centralizer (E' : Set _) := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hUt, ← PU.centralizer_map_mulEquiv]
    have hrelE' : (Subgroup.centralizer (E' : Set (puAmalgam h.le).Universal)).relIndex U =
        2 ^ k := by
      rw [hE', PU.centralizer_map_mulEquiv]
      conv_lhs => rw [← hUt]
      rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj t).injective, hrelE]
    rw [hRt]
    by_cases hYeq : U ⊓ Subgroup.centralizer (E' : Set (puAmalgam h.le).Universal) =
        U ⊓ Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal)
    ·
      set E := ZM _ γ ⊔ E' with hE
      have hE2 : IsPGroup 2 E := (hT2.to_le hQαρ).to_le (sup_le hZγα hE'α)
      have hEc : U ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) =
          U ⊓ Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal) := by
        rw [hE, S512R.centralizer_sup_eq, ← inf_assoc, inf_right_comm, hYeq, inf_assoc, inf_idem]
      have hrelEE : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex U =
          2 ^ k := by
        rw [← Subgroup.inf_relIndex_right, inf_comm, hEc, inf_comm, Subgroup.inf_relIndex_right,
          hrelE]
      have hq' : 2 ^ k ≤ (Qv _ μ₁).relIndex (ZM _ γ) :=
        S512T.le_relIndex_qv_zm h hb4 hd (ms22_iii _ hyp hb0 h.centHyp hcμ)
      have key := commutator_uSub_le_of_relIndex h hd hμM (sup_le hZγμ hE'μ) hE2 le_sup_left
        hrelEE hq'
      exact ((Subgroup.commutator_mono le_rfl le_sup_right).trans key).trans le_sup_right
    ·
      have hcov := uSub_le_sup_of_ne h hd hμM hZγμ hE'μ hrelE hrelE' (Ne.symm hYeq)
      have h1 : ⁅U, E'⁆ ≤ ⁅(U ⊓ Subgroup.centralizer (ZM _ γ : Set _)) ⊔
          (U ⊓ Subgroup.centralizer (E' : Set _)), E'⁆ :=
        Subgroup.commutator_mono hcov le_rfl
      have hAB : U ⊓ Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal) ≤
          Subgroup.normalizer ((U ⊓ Subgroup.centralizer (E' : Set _) : Subgroup _) :
            Set (puAmalgam h.le).Universal) := by
        refine S5.le_normalizer_of_commute fun n hn w hw => ?_
        exact (isElemAbelian_zm _ hyp hb0 hμM).1.is_comm.comm ⟨n, hUZ hn.1⟩ ⟨w, hUZ hw.1⟩
          |> congrArg Subtype.val
      have h2 := commutator_sup_le_left hAB (inf_le_right : U ⊓ Subgroup.centralizer
        (E' : Set (puAmalgam h.le).Universal) ≤ _)
      refine (h1.trans h2).trans (le_sup_of_le_left ?_)
      rw [← hYc]
      exact Subgroup.commutator_mono le_rfl hE'α
  set S := ⨅ t : ↥(Qv _ ρ), X'.map (MulAut.conj (t : (puAmalgam h.le).Universal)).toMonoidHom
    with hSdef
  have hSX' : S ≤ X' := by
    intro s hs
    have h1 := Subgroup.mem_iInf.1 hs ⟨1, one_mem _⟩
    rw [mem_map_conj] at h1
    simpa using h1
  have hRS : R₂ ≤ S := by
    rw [hSdef, le_iInf_iff]
    intro t
    have key : R₂.map (MulAut.conj (t : (puAmalgam h.le).Universal)⁻¹).toMonoidHom ≤ X' := by
      refine le_inf (hR₂t _ (inv_mem t.2)) ?_
      have := Subgroup.map_mono
        (f := (MulAut.conj (t : (puAmalgam h.le).Universal)⁻¹).toMonoidHom) hRXh
      rwa [map_conj_eq_of_mem_normalizer (hXhn (inv_mem (hTρα t.2)))] at this
    have := (map_conj_le_iff (t : (puAmalgam h.le).Universal)⁻¹).1 key
    rwa [inv_inv] at this
  set Z₀ := imM h.le (Zq M L) with hZ₀def
  have hZ₀n : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (Z₀ : Set (puAmalgam h.le).Universal) := by
    rw [puAmalgam.stab_baseA]
    exact S5B.imM_le_normalizer h.le (S5.le_normalizer_cXL h)
  have hRn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer ((S ⊔ Z₀ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    rw [← hgen]
    refine sup_le (le_normalizer_sup (le_normalizer_iInf_map_conj _ _) (hTρα.trans hZ₀n)) ?_
    refine le_normalizer_sup_of_commutator_le (hZst.trans hZ₀n) ?_
    rw [Subgroup.commutator_le]
    intro s hs z hz
    rw [← commutatorElement_inv]
    exact Subgroup.mem_sup_right (Z₀.inv_mem (hcommX s (hSX' hs) z hz))
  have hZ₀X : Z₀ ≤ XM _ (baseA (puAmalgam h.le)) := by
    rw [S5B.xm_baseA_eq h]
    exact imM_mono h.le inf_le_left
  have hSXα : S ≤ XM _ (baseA (puAmalgam h.le)) := hSX'.trans (inf_le_left.trans hXX)
  have hSc : Nat.card S < (2 ^ k) ^ 4 := by
    have hfin : Finite ↥(U ⊓ Subgroup.centralizer
        (Qv _ (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal)) := by
      have := S310.finite_stab_of_isMVtx h hμM
      exact Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left.trans
        ((S5B.uSub_le_zm h.le μ₁).trans ((zm_le_qv_self _ hμM hb0).trans (qv_le_stab _ _)))))
    have h1 : Nat.card ↥(U ⊓ Subgroup.centralizer
        (Qv _ (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal)) ≤ (2 ^ k) ^ 3 :=
      S512F.card_uSub_inf_centralizer_le h hd hμM hQαμ hlarge
    have h2 : S ≤ U ⊓ Subgroup.centralizer
        (Qv _ (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) :=
      le_inf (hSX'.trans (inf_le_left.trans hXU)) (hSXα.trans hXαQ)
    have h3 := Subgroup.card_le_of_le h2
    have h4 : (2 ^ k) ^ 3 < (2 ^ k) ^ 4 := Nat.pow_lt_pow_right hk1 (by norm_num)
    omega
  have hcen := le_stabCenter_of_le_sup h32 hq2 h hmin hb hd (sup_le hSXα hZ₀X) hRn hSXα le_rfl hSc
  have hRc : R₂ ≤ stabCenter _ (baseA (puAmalgam h.le)) := hRS.trans (le_sup_left.trans hcen)
  apply hTY
  rw [hYc]
  refine le_normalizer_of_map_conj_le fun t ht => ?_
  have htα : t ∈ stab _ (baseA (puAmalgam h.le)) := hTρα ht
  have htμ : t ∈ stab _ μ₁ := hTμ ht
  have hUt : U.map (MulAut.conj t).toMonoidHom = U := by
    rw [hUdef, ← S5B.uSub_smul h.le hLn, (mem_stab _).1 htμ]
  have hZtμ : (ZM _ γ).map (MulAut.conj t).toMonoidHom ≤ stab _ μ₁ := by
    have := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hZγμ
    rwa [← stab_smul, (mem_stab _).1 htμ] at this
  have heq : ⁅U, ZM _ γ⁆ = ⁅U, (ZM _ γ).map (MulAut.conj t).toMonoidHom⁆ := by
    conv_rhs => rw [← hUt]
    rw [← Subgroup.map_commutator, ← hR₂def, S512R.map_conj_eq_of_le_stabCenter h hRc htα]
  have key := S5B.uSub_inf_centralizer_eq h hd hμM hZγμ hZtμ heq
  rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hUt, ← PU.centralizer_map_mulEquiv,
    ← key]

theorem threeAlt2L_holds (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (h58 : S5B.S58) (hq2 : S5B.Q2Cent) : S512R.ThreeAlt2L := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hch hq1 hq h56 hline hXU g hg x hx hc55
    hμeq hL hTY hlarge
  exact (false_of_threeAlt2 h32 hX2 h52 h54 h58 hq2 h hmin hb4 hd hch hq1 hq h56 hline hg hx hc55
    hμeq hL hTY hlarge).elim

end S512H

end CFSG.Quasithin.MS93
