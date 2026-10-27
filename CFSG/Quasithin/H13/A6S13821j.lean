module

public import CFSG.Quasithin.Background.OrbSupStab
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge
public import CFSG.Quasithin.EmptyFaithful.SzN15Vocab
public import CFSG.Quasithin.H13.L32AC36e
public import CFSG.Quasithin.H13.L32AC47k

public section

namespace CFSG.Quasithin.H13.A6.A6M22

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.SzN15 (fixMod)

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem mem_subM_of_normal {I : Subgroup G} (hHI : H ≤ Subgroup.normalizer (I : Set G))
    (w : ↥(tildeOf V₁ (conjClosure I H))) : w ∈ subM V₁ (conjClosure I H) I := by
  have hcI : conjClosure I H = I :=
    le_antisymm (conjClosure_le fun _ hh i hi => (Subgroup.mem_normalizer_iff.mp (hHI hh) i).mp hi)
      (le_conjClosure I H)
  have key : tildeOf V₁ (conjClosure I H) = tildeOf V₁ I := by rw [hcI]
  rw [mem_subM_iff]
  exact key.le w.2

theorem autIH_le_stabSub {I : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hF : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I)
    (hHI : H ≤ Subgroup.normalizer (I : Set G)) {X : Subgroup G} (hXH : X ≤ H) :
    autIH V₁ I H X ≤ CFSG.Quasithin.stabSub (subM V₁ (conjClosure I H) I) := by
  intro t ht
  rw [autIH_eq_map hF hXH] at ht
  obtain ⟨x, -, rfl⟩ := ht
  exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁ (hF.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) x).mpr (hHI x.2)

omit [Finite G] in
theorem autIH_inf_centSub {I : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hHI : H ≤ Subgroup.normalizer (I : Set G)) (X : Subgroup G) :
    autIH V₁ I H X ⊓ CFSG.Quasithin.centSub (subM V₁ (conjClosure I H) I) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨-, hg⟩
  rw [Subgroup.mem_bot]
  exact MulEquiv.ext fun w => hg w (mem_subM_of_normal hHI w)

theorem card_autIH_m22 {I : Subgroup G}
    (hF : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hM : IsSporadic .M22 (L32A.cStar K)) : Nat.card ↥(autIH V₁ I H K) = 443520 := by
  have := factElem hF hIU
  have hS := L32A.C.isSimpleGroup_of_m22 hM
  have hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := (L32A.C.cStarEquiv K).symm.isSimpleGroup
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map hF (le_of_mem_cComp hF.K_cComp)]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS' hne
  rw [← Nat.card_congr e.toEquiv, ← Nat.card_congr (L32A.C.cStarEquiv K).toEquiv]
  exact L32A.C.card_of_m22 hM

theorem mem_stabSub_of_eq_orbSup {W : Type} [CommGroup W] {T : Subgroup (MulAut W)}
    {U : Subgroup W} (h : U = orbSup T U) {t : MulAut W} (ht : t ∈ T) :
    t ∈ CFSG.Quasithin.stabSub U :=
  CFSG.Quasithin.StabLat.mem_stabSub_of_eq_orbSup h ht

theorem exists_I (h56 : AsB56) (hD310 : D310) (hD391 : D391)
    (hI4 : Insp4) (hSQ : SQTKGroup ↥H) (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hHeq : H = conjClosure K T ⊔ T)
    (hM : IsSporadic .M22 (L32A.cStar K)) :
    ∃ I : Subgroup G, V₁ ≤ I ∧ ∃ hIU : I ≤ conjClosure Vp H,
      IsIrrPlusTildeT hF hIU ∧ H ≤ Subgroup.normalizer (I : Set G) ∧
        tildeOf V₁ I = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirrT := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hFct := factElem hF hIU
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirrT
  have hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G) :=
    K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have h4 := (F918_4' hF hSQ hK₀ hV₁I hIU W hW hirrU hD310 hD391 hI4).2
  have hHI : H ≤ Subgroup.normalizer (I : Set G) := by
    rcases h4 with h4 | (⟨hVT, -⟩ | h3)
    · exact h4
    · have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
        intro t ht
        have hst := mem_stabSub_of_eq_orbSup hVT (actH_mem_autIH_of_mem (I := I) hF hTH ht)
        exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
          (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
          (le_conjClosure I H) ⟨t, hTH ht⟩).mp hst
      rw [hHeq]
      exact sup_le hKI hTI
    · exact (L32A.C.false_of_d310Two_card h3 (Or.inl (card_autIH_m22 hF hIU hnt hM))).elim
  have hcI : conjClosure I H = I :=
    le_antisymm (conjClosure_le fun _ hh i hi => (Subgroup.mem_normalizer_iff.mp (hHI hh) i).mp hi)
      (le_conjClosure I H)
  have hS' : IsSimpleGroup (KBar K) := L32A.C.isSimpleGroup_of_m22 hM
  have hZ : ∀ x ∈ conjClosure K T,
      (∀ k' ∈ conjClosure K T, x * k' * x⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) → x ∈ pCoreOf 2 H := by
    rw [hK₀]
    exact hZ_comp hF.K_cComp hS'
  have hI := isIrrPlusTilde_of_module hF hV₁I hIU hirrT
  have hNo : HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 H) := by
    have hK' : K ∈ cComp (conjClosure K T ⊔ T) := hHeq ▸ hF.K_cComp
    have hKn : (K.subgroupOf (conjClosure K T ⊔ T)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK'), ← hHeq]
      exact hK₀ ▸ hF.K₀_normal
    have hXeq : conjClosure K T ⊔ T = K ⊔ T := by rw [hK₀]
    have hsq : SQTKGroup ↥(conjClosure K T ⊔ T) := hHeq ▸ hSQ
    have h := L32A.C.noFaithfulFF_m22 h56 hK' hKn hXeq le_sup_right hF.sylow_H.2.1 hsq hM
    have hp : pCoreOf 2 (conjClosure K T ⊔ T) = pCoreOf 2 H := by rw [← hHeq]
    rw [hp] at h
    exact h
  have h7 := hF.F918_7' hHeq hZ hV₁I hIU hI hNo
  rw [hcI] at h7
  exact ⟨I, hV₁I, hIU, hirrT, hHI, h7⟩

theorem code_m22
    (hIrr : MathieuSmallIrr22) (hA21 : AsA21SQTKSection) (hSQ : SQTKGroup ↥H)
    (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K)
    (hM : IsSporadic .M22 (L32A.cStar K)) {I : Subgroup G} (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hirrT : IsIrrPlusTildeT hF hIU)
    (hHI : H ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] :
    MathieuCode22 (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf (subM V₁ (conjClosure I H) I)) := by
  set V' := subM V₁ (conjClosure I H) I with hV'
  set L' := autIH V₁ I H K with hL'
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hirr' : V' ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) V') (autIH V₁ I H T) := hirrT
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
  have hD3 : D3Std (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) L' V' :=
    ⟨hD, hA.qhat_VT hD.exp, hirr'⟩
  have hMp : autIH V₁ I H (conjClosure K T) = L' := by rw [hK₀]
  have hT := autIH_le_stabSub hF hIU hV₁I hHI hF.T_le_H
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD hT
  have hQS := lred3_qsec hD hMp hO2
  have hB4 := lred3_b4Hyp hA21 hD hMp hO2
  have hqh := lred3_qhatOf_autSec hD3 hMp hT
  have hq := lred3_qOf_autSec hD3 hMp hT (hA.qOf_VT hD.exp)
  have hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    have := L32A.C.isSimpleGroup_of_m22 hM
    (L32A.C.cStarEquiv K).symm.isSimpleGroup
  have hne : L' ≠ ⊥ := by
    rw [hL', autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨e3⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS' hne
  have e2 := autSubEquivOfFaithful (autIH_le_stabSub hF hIU hV₁I hHI hKH) (autIH_inf_centSub hHI K)
  have e1 := B5.secEquiv (autSub L' V') (InternalSec.le_stabSub_top _) hQS.stabKC hQS.faithful
  obtain ⟨eM⟩ := hM
  have e : ↥(autSec (autSub L' V') ⊤
      ((V' ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf V')) ≃* ↥NativeSporadic.M22 :=
    e1.symm.trans (e2.symm.trans (e3.symm.trans ((L32A.C.cStarEquiv K).symm.trans eM)))
  have hsM := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hs := e.isSimpleGroup
  have hType : B45TypeSpor .M22 ↥(autSec (autSub L' V') ⊤
      ((V' ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf V')) :=
    ⟨L32A.C.center_eq_bot_of_isSimpleGroup hs
      (L32A.C.exists_noncomm_of_isQuasisimple hB4.2.2.1), ⟨e⟩⟩
  have hexp : ∀ v : Sec (⊤ : Subgroup ↥V')
      ((V' ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf V'), v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow]
      have h2 : w ^ 2 = 1 := Subtype.ext (Subtype.ext (by simp [hD.exp]))
      rw [h2, QuotientGroup.mk_one]
  rcases L32A.C.code22_of_qhat hIrr hexp hB4 hType hqh with ⟨hc, -⟩ | ⟨-, hc⟩
  · exact InternalSec.mathieuCode22_of_autSec hQS.stabKC hQS.faithful hc
  · exact absurd (hc.trans_le hq) (lt_irrefl _)

section Psi

variable {I : Subgroup G} [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem actH_mem_stabSub_I (hF : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G)) (x : ↥H) :
    actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x ∈
      CFSG.Quasithin.stabSub (subM V₁ (conjClosure I H) I) :=
  (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁ (hF.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) x).mpr (hHI x.2)

@[expose] noncomputable def psiI (hF : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G)) :
    ↥H →* MulAut ↥(subM V₁ (conjClosure I H) I) :=
  (resHom (subM V₁ (conjClosure I H) I)).comp
    ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)).codRestrict _
      (actH_mem_stabSub_I hF hIU hV₁I hHI))

theorem psiI_apply (hF : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G)) (x : ↥H)
    (w : ↥(subM V₁ (conjClosure I H) I)) :
    ((psiI hF hIU hV₁I hHI x w : ↥(subM V₁ (conjClosure I H) I)) :
        ↥(tildeOf V₁ (conjClosure I H))) =
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x w :=
  rfl

theorem map_psiI (hF : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G)) {X : Subgroup G}
    (hXH : X ≤ H) :
    (X.subgroupOf H).map (psiI hF hIU hV₁I hHI) =
      autSub (autIH V₁ I H X) (subM V₁ (conjClosure I H) I) := by
  ext φ
  rw [mem_autSub, autIH_eq_map hF hXH]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨_, actH_mem_stabSub_I hF hIU hV₁I hHI x⟩, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨x, hx, hxg⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    have hg : (⟨_, actH_mem_stabSub_I hF hIU hV₁I hHI x⟩ :
        ↥(CFSG.Quasithin.stabSub (subM V₁ (conjClosure I H) I))) = g := Subtype.ext hxg
    rw [← hg]
    rfl

theorem psiI_eq_one_of_mem_pCoreOf (hF : HypF918 T V L V₁ Vp H K)
    (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I)
    (hHI : H ≤ Subgroup.normalizer (I : Set G)) {x : ↥H} (hx : (x : G) ∈ pCoreOf 2 H) :
    psiI hF hIU hV₁I hHI x = 1 := by
  have h1 := hF.actH_eq_one_of_mem_pCoreOf hIU hx
  refine MulEquiv.ext fun w => Subtype.ext ?_
  show actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x
      (w : ↥(tildeOf V₁ (conjClosure I H))) = (w : ↥(tildeOf V₁ (conjClosure I H)))
  rw [h1]
  rfl

theorem four_mul_card_le_fixMod (hF : HypF918 T V L V₁ Vp H K)
    (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I) (hHI : H ≤ Subgroup.normalizer (I : Set G))
    {Y : Subgroup G} (hV₁Y : V₁ ≤ Y) (hYI : Y ≤ I) (hK₀ : conjClosure K T = K) {R : Subgroup G}
    (hR : ∀ r ∈ R, ∀ v ∈ Y, r * v * r⁻¹ * v⁻¹ ∈ V₁)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) {x : G} (hxK : x ∈ K)
    (hfpf : ∀ v ∈ Y, x * v * x⁻¹ * v⁻¹ ∈ V₁ → v ∈ V₁)
    (hY4 : V₁.relIndex Y = 4)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) :
    4 * Nat.card ↥((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf (subM V₁ (conjClosure I H) I)) ≤
      Nat.card ↥(fixMod ((R.subgroupOf H).map (psiI hF hIU hV₁I hHI)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓
          fixV (autIH V₁ I H (conjClosure K T))).subgroupOf (subM V₁ (conjClosure I H) I))) := by
  set IH := conjClosure I H with hIH'
  set V' := subM V₁ IH I with hV'
  set Mp := autIH V₁ I H (conjClosure K T) with hMp
  set C := (V' ⊓ fixV Mp).subgroupOf V' with hC
  set Ψ := psiI hF hIU hV₁I hHI with hΨ
  set Rc := (R.subgroupOf H).map Ψ with hRc
  have hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G) := hF.conjClosure_le_normalizer_V₁ hIU
  have hIH : H ≤ Subgroup.normalizer (IH : Set G) := le_normalizer_conjClosure I H
  have hYIH : Y ≤ IH := hYI.trans (le_conjClosure I H)
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hsub : subM V₁ IH Y ≤ V' := fun w hw => secImg_mono hYI hw
  set Yt := (subM V₁ IH Y).subgroupOf V' with hYt
  have hYt4 : Nat.card Yt = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsub).toEquiv,
      card_subM hIHN hV₁Y hYIH, hY4]
  have hrep : ∀ w ∈ Yt, ∃ v : G, ∃ hv : v ∈ Y,
      (w : ↥(tildeOf V₁ IH)) = modMk hIHN v (hYIH hv) := by
    intro w hw
    obtain ⟨a, haV, ha⟩ := mem_secImg.mp (show ((w : ↥(tildeOf V₁ IH)) :
      SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ Y from hw)
    exact ⟨a, haV, Subtype.ext ha.symm⟩
  have hMpK : Mp = autIH V₁ I H K := by rw [hMp, hK₀]
  have hYtC : C ⊓ Yt = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwC, hwYt⟩
    obtain ⟨v, hv, hwv⟩ := hrep w hwYt
    have hxK₀ : x ∈ conjClosure K T := le_conjClosure K T hxK
    have hxMp := actH_mem_autIH_of_mem (I := I) hF hF.K₀_le_H hxK₀
    have hwC' : (w : ↥(tildeOf V₁ IH)) ∈ V' ⊓ fixV Mp := Subgroup.mem_subgroupOf.mp hwC
    have hfix := hwC'.2 _ hxMp
    rw [hwv] at hfix
    have hc := hF.commutator_mem_of_actH_fix hIU (hYIH hv) hfix
    have hv1 := hfpf v hv hc
    rw [Subgroup.mem_bot]
    refine Subtype.ext (Subtype.ext ?_)
    rw [hwv]
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (x := ⟨v, hIHN (hYIH hv)⟩)).mpr hv1
  have hYtF : Yt ≤ fixMod Rc ⊤ C := by
    intro w hw
    refine ⟨Subgroup.mem_top w, fun r hr => ?_⟩
    obtain ⟨y, hyR, rfl⟩ := hr
    have hyR' : (y : G) ∈ R := Subgroup.mem_subgroupOf.mp hyR
    obtain ⟨v, hv, hwv⟩ := hrep w hw
    have h1 : Ψ y w = w := by
      apply Subtype.ext
      rw [psiI_apply, hwv, actH_modMk hF.H_le_normalizer_V₁ hIHN hIH y (hYIH hv)]
      apply Subtype.ext
      show secMk _ _ ⟨(y : G) * v * (y : G)⁻¹, _⟩ = secMk _ _ ⟨v, _⟩
      rw [secMk_eq_secMk_iff]
      have hc := hR y hyR' v hv
      have hyv : (y : G) * v * (y : G)⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hRY hyR') v).mp hv
      show ((y : G) * v * (y : G)⁻¹)⁻¹ * v ∈ V₁
      set b := (y : G) * v * (y : G)⁻¹ with hb
      have e : b⁻¹ * v = (b * v⁻¹)⁻¹ := by
        rw [show (b * v⁻¹)⁻¹ = v * b⁻¹ by group]
        exact hYc _ (inv_mem hyv) v hv
      rw [e]
      exact inv_mem hc
    rw [h1, mul_inv_cancel]
    exact C.one_mem
  have hCF : C ≤ fixMod Rc ⊤ C := by
    intro c hc
    refine ⟨Subgroup.mem_top c, fun r hr => ?_⟩
    obtain ⟨y, -, rfl⟩ := hr
    refine C.mul_mem ?_ (C.inv_mem hc)
    have hc' : (c : ↥(tildeOf V₁ IH)) ∈ V' ⊓ fixV Mp := Subgroup.mem_subgroupOf.mp hc
    refine Subgroup.mem_subgroupOf.mpr ⟨(Ψ y c).2, fun m hm => ?_⟩
    rw [psiI_apply]
    have hyK : (y : G) ∈ Subgroup.normalizer (K : Set G) := hK₀ ▸ hF.K₀_normal y.2
    have hyN := actH_mem_normalizer_autIH (I := I) hF y.2 hyK
    rw [← hMpK] at hyN
    set a := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) y with ha
    have hm' : a⁻¹ * m * a⁻¹⁻¹ ∈ Mp := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) m).mp hm
    rw [inv_inv] at hm'
    have h2 := hc'.2 _ hm'
    have h3 : m (a (c : ↥(tildeOf V₁ IH))) = a ((a⁻¹ * m * a) (c : ↥(tildeOf V₁ IH))) := by
      simp [MulAut.mul_apply]
    rw [h3, h2]
  have hsupF : Yt ⊔ C ≤ fixMod Rc ⊤ C := sup_le hYtF hCF
  have hcomm : Yt ≤ Subgroup.normalizer (C : Set ↥V') := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro c
    rw [mul_comm g c, mul_inv_cancel_right]
  have hcard := L32A.C.card_sup_eq hcomm
  have h1 := Subgroup.relIndex_mul_card C Yt
  rw [hYtC, Subgroup.card_bot, mul_one, hYt4] at h1
  rw [h1] at hcard
  rw [← hcard]
  exact Subgroup.card_le_of_le hsupF

end Psi

end CFSG.Quasithin.H13.A6.A6M22
