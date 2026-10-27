module

public import CFSG.Quasithin.H13.A6S13821j
public import CFSG.Quasithin.H13.L32AC47o

public section

namespace CFSG.Quasithin.H13.A6.A6L32

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Vol2Native.A312L.Seven

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem autIH_le_stabSub_of (hF : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I) [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    {X : Subgroup G} (hXH : X ≤ H) (hXI : X ≤ Subgroup.normalizer (I : Set G)) :
    autIH V₁ I H X ≤ CFSG.Quasithin.stabSub (subM V₁ (conjClosure I H) I) := by
  intro g hg
  rw [autIH_eq_map hF hXH] at hg
  obtain ⟨s, hs, rfl⟩ := hg
  exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁ (hF.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) s).mpr
    (hXI (Subgroup.mem_subgroupOf.mp hs))

theorem autSec_eq_of_T_le (hA21 : AsA21SQTKSection) (hSQ : SQTKGroup ↥H)
    (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K)
    (hP : IsPSL 3 2 1 (L32A.cStar K)) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirrT : IsIrrPlusTildeT hF hIU) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] :
    autSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) ⊤
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)) =
    autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)) := by
  classical
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I))
        (autIH V₁ I H T) := hirrT
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
  have hD3 : D3Std (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T))
      (autIH V₁ I H T) (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I) := ⟨hD, hA.qhat_VT hD.exp, hirr'⟩
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK₀]
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hT := autIH_le_stabSub_of hF hIU hV₁I hF.T_le_H hTI
  have hLs := autIH_le_stabSub_of hF hIU hV₁I hKH hKI'
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD hT
  have hQS := lred3_qsec hD hMp hO2
  have hB4 := lred3_b4Hyp hA21 hD hMp hO2
  have hqh := lred3_qhatOf_autSec hD3 hMp hT
  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := slThree_isSimple
  have hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    ((L32A.C.cStarEquiv K).symm.trans φ).isSimpleGroup
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨e3⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS' hne
  have hL'S : IsSimpleGroup ↥(autIH V₁ I H K) := e3.symm.isSimpleGroup
  have hLnc : ¬ autIH V₁ I H K ≤ centSub (subM V₁ (conjClosure I H) I) := by
    intro hle
    apply ne_of_lt hirr'.1.2.2.2.1
    ext w
    constructor
    · exact fun h => h.1
    · intro hw
      refine ⟨hw, fun a => ?_⟩
      have ha : (a : MulAut _) ∈ autIH V₁ I H K := hMp ▸ a.2
      exact hle ha w hw
  have hfaith := inf_centSub_eq_bot_of_isSimpleGroup hL'S hLs hLnc
  let e2 := autSubEquivOfFaithful hLs hfaith
  let e1 := B5.secEquiv _ (InternalSec.le_stabSub_top _) hQS.stabKC hQS.faithful
  let eLs := e1.symm.trans (e2.symm.trans (e3.symm.trans ((L32A.C.cStarEquiv K).symm.trans φ)))
  have hZ := L32A.C.center_eq_bot_of_mulEquiv eLs L32A.C.sl3_center_eq_bot
  have hType : B42TypeL32 _ :=
    ⟨hZ, isPSL_three_two_iff.mpr ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans eLs)⟩⟩
  obtain ⟨eL⟩ := B42L2.exists_gl32_of_model hZ hType.2
  have hexp : ∀ v : Sec (⊤ : Subgroup ↥(subM V₁ (conjClosure I H) I))
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)), v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow]
      have h2 : w ^ 2 = 1 := Subtype.ext (Subtype.ext (by simp [hD.exp]))
      rw [h2, QuotientGroup.mk_one]
  have hS2 : ∀ v : Sec (⊤ : Subgroup ↥(subM V₁ (conjClosure I H) I))
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)), v * v = 1 := fun v => by
    rw [← pow_two]
    exact hexp v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hS2
  have hq1 := asB45L32_holds _ hexp _ _ hB4 hType hqh
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender (isFFModule_of_qhatOf_le_one hexp hq1)
  exact B42L2.eq_of_l32 θ hB4 hZ eL hA

theorem qsec_of_T_le (hSQ : SQTKGroup ↥H) (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirrT : IsIrrPlusTildeT hF hIU) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] :
    InternalSec.QSec
      (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I))
      (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I))
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)) := by
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I))
        (autIH V₁ I H T) := hirrT
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK₀]
  have hT := autIH_le_stabSub_of hF hIU hV₁I hF.T_le_H hTI
  exact lred3_qsec hD hMp (lred3_pCoreOf_autSub_sup_eq_bot hD hT)

theorem exists_centSec_of_autSec_eq (hSQ : SQTKGroup ↥H)
    (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hirrT : IsIrrPlusTildeT hF hIU)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hGL : autSec (autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
        (subM V₁ (conjClosure I H) I)) ⊤
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)) =
    autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
      ((subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)))
    {t : G} (ht : t ∈ T) :
    ∃ k ∈ K, ∃ hk : k ∈ H, ∀ w ∈ subM V₁ (conjClosure I H) I,
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          (⟨k, hk⟩⁻¹ * ⟨t, hF.T_le_H ht⟩) w * w⁻¹ ∈
        subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T)) := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hT := autIH_le_stabSub_of hF hIU hV₁I hTH hTI
  have hQS := qsec_of_T_le hSQ hF hK₀ hV₁I hIU hirrT hTI
  set ψ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hψ
  have hψt : ψ ⟨t, hTH ht⟩ ∈ autIH V₁ I H T := actH_mem_autIH_of_mem hF hTH ht
  obtain ⟨τ, hτ⟩ : ∃ τ : MulAut ↥(subM V₁ (conjClosure I H) I),
      τ = resHom _ ⟨ψ ⟨t, hTH ht⟩, hT hψt⟩ := ⟨_, rfl⟩
  have hτΛ : τ ∈ autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
      (subM V₁ (conjClosure I H) I) :=
    mem_autSub.mpr ⟨⟨ψ ⟨t, hTH ht⟩, hT hψt⟩, Subgroup.mem_sup_right hψt, hτ.symm⟩
  have hσt : B5.secHom _ (InternalSec.le_stabSub_top _) hQS.stab ⟨τ, hτΛ⟩ ∈
      autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓
          fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
            (subM V₁ (conjClosure I H) I)) := by
    rw [← hGL, ← B5.range_secHom _ (InternalSec.le_stabSub_top _) hQS.stab]
    exact ⟨_, rfl⟩
  rw [← B5.map_secHom_eq_autSec _ (InternalSec.le_stabSub_top _) hQS.stab hQS.le] at hσt
  obtain ⟨κ, hκK, hκσ⟩ := hσt
  have hker := L32A.C.inv_apply_mul_inv_mem_of_secHom_eq (InternalSec.le_stabSub_top _) hQS.stab hκσ
  obtain ⟨g, hgL, hgκ⟩ := mem_autSub.mp (Subgroup.mem_subgroupOf.mp hκK)
  have hgL' := hgL
  rw [autIH_eq_map hF hKH] at hgL'
  obtain ⟨⟨k, hkH⟩, hkK, hkg⟩ := hgL'
  refine ⟨k, Subgroup.mem_subgroupOf.mp hkK, hkH, fun w hw => ?_⟩
  have h1 := hker ⟨w, hw⟩ trivial
  subst hτ
  rw [← hgκ, Subgroup.mem_subgroupOf] at h1
  have h2 : (g : MulAut _)⁻¹ (ψ ⟨t, hTH ht⟩ w) * w⁻¹ ∈
      subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T)) := h1
  rw [map_mul, map_inv, MulAut.mul_apply, hkg]
  exact h2

theorem actH_mem_stabSub_inf (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {h : G} (hh : h ∈ H)
    (hnI : h ∈ Subgroup.normalizer (I : Set G)) (hnK : h ∈ Subgroup.normalizer (K : Set G)) :
    actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨h, hh⟩ ∈
      CFSG.Quasithin.stabSub (subM V₁ (conjClosure I H) I ⊓
        fixV (autIH V₁ I H (conjClosure K T))) := by
  have hMpK : autIH V₁ I H (conjClosure K T) =
      (K.subgroupOf H).map (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
    rw [autIH_eq_map hF hF.K₀_le_H, hK₀]
  refine L32A.C.mem_stabSub_inf ((actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
    (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
    (le_conjClosure I H) ⟨h, hh⟩).mpr hnI) (L32A.C.mem_stabSub_fixV_of_conj ?_ ?_)
  · intro m hm
    rw [hMpK] at hm ⊢
    obtain ⟨k', hk', rfl⟩ := hm
    refine ⟨⟨h, hh⟩ * k' * ⟨h, hh⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_,
      by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp hnK _).mp (Subgroup.mem_subgroupOf.mp hk')
  · intro m hm
    rw [hMpK] at hm ⊢
    obtain ⟨k', hk', rfl⟩ := hm
    refine ⟨⟨h, hh⟩⁻¹ * k' * ⟨h, hh⟩, Subgroup.mem_subgroupOf.mpr ?_,
      by rw [map_mul, map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnK) _).mp
      (Subgroup.mem_subgroupOf.mp hk')
    simpa using this

theorem mem_pCoreOf_of_centSec (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hP : IsPSL 3 2 1 (L32A.cStar K)) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hirrT : IsIrrPlusTildeT hF hIU)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {c : G} (hcK : c ∈ K)
    (hcc : actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
      ⟨c, le_of_mem_cComp hF.K_cComp hcK⟩ ∈ centSec (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓
          fixV (autIH V₁ I H (conjClosure K T)))) : c ∈ pCoreOf 2 K := by
  classical
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  set ψ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hψ
  set V' := subM V₁ (conjClosure I H) I with hV'
  set D := V' ⊓ fixV (autIH V₁ I H (conjClosure K T)) with hD
  have hirr' : V' ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) V') (autIH V₁ I H T) := hirrT
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hstab : ∀ h (hh : h ∈ H), h ∈ Subgroup.normalizer (I : Set G) →
      ψ ⟨h, hh⟩ ∈ CFSG.Quasithin.stabSub V' := fun h hh hn =>
    (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁ (hF.conjClosure_le_normalizer_V₁ hIU)
      (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) ⟨h, hh⟩).mpr hn
  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := slThree_isSimple
  set π₀ : ↥K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' _) with hπ₀
  have hπ₀s : Function.Surjective π₀ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ k' : ↥K, π₀ k' = 1 ↔ (k' : G) ∈ pCoreOf 2 K := fun k' => by
    rw [hπ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let N : Subgroup ↥K := (centSec V' D).comap (ψ.comp (Subgroup.inclusion hKH))
  have hNn : N.Normal := ⟨fun n hn g => by
    show ψ (Subgroup.inclusion hKH (g * n * g⁻¹)) ∈ centSec V' D
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    exact L32A.C.conj_mem_centSec (hstab _ _ (hKI' g.2))
      (actH_mem_stabSub_inf hF hK₀ hV₁I hIU _ (hKI' g.2) (Subgroup.le_normalizer g.2)) hn⟩
  have hNm := hNn.map π₀ hπ₀s
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π₀) with hb | htop
  · have hmem : π₀ ⟨c, hcK⟩ ∈ N.map π₀ := ⟨⟨c, hcK⟩, hcc, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact (hker₀ _).mp hmem
  ·
    exfalso
    have hall : ∀ k' (hk' : k' ∈ K), ψ ⟨k', hKH hk'⟩ ∈ centSec V' D := by
      intro k' hk'
      have hmem : π₀ ⟨k', hk'⟩ ∈ N.map π₀ := by rw [htop]; trivial
      obtain ⟨n, hn, hne'⟩ := hmem
      have h1 : π₀ (n⁻¹ * ⟨k', hk'⟩) = 1 := by rw [map_mul, map_inv, hne', inv_mul_cancel]
      have h2 := (hker₀ _).mp h1
      have h3 := actH_eq_one_of_mem_pCoreOf_K (I := I) hF hIU h2 (hKH (n⁻¹ * ⟨k', hk'⟩).2)
      have e3 : (⟨k', hKH hk'⟩ : ↥H) = Subgroup.inclusion hKH n *
          ⟨_, hKH (n⁻¹ * ⟨k', hk'⟩).2⟩ := Subtype.ext (by simp)
      rw [e3, map_mul]
      have h3' : ψ ⟨_, hKH (n⁻¹ * ⟨k', hk'⟩).2⟩ = 1 := h3
      rw [h3', mul_one]
      exact hn
    have hMpK : autIH V₁ I H (conjClosure K T) = (K.subgroupOf H).map ψ := by
      rw [autIH_eq_map hF hF.K₀_le_H, hK₀]
    apply ne_of_lt hirr'.1.2.2.2.1
    have hcomm := hirr'.1.2.2.1
    have hle : V' ≤ D := by
      rw [← hcomm]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨a, l, hl, rfl⟩
      have ha' : (a : MulAut _) ∈ (K.subgroupOf H).map ψ := hMpK ▸ a.2
      obtain ⟨k', hk', hk'a⟩ := ha'
      have h1 := (hall k' (Subgroup.mem_subgroupOf.mp hk')).2 l hl
      rw [show (⟨(k' : G), hKH (Subgroup.mem_subgroupOf.mp hk')⟩ : ↥H) = k' from rfl, hk'a] at h1
      exact h1
    ext w
    exact ⟨fun h => h.1, fun hw => ⟨hw, fun a => (hle hw).2 a a.2⟩⟩

theorem false_of_centSec (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K)
    (hP : IsPSL 3 2 1 (L32A.cStar K)) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirrT : IsIrrPlusTildeT hF hIU) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {t : G} (ht : t ∈ T)
    (hout : ∀ k ∈ K, ∃ x ∈ K, t * k⁻¹ * x * (t * k⁻¹)⁻¹ * x⁻¹ ∉ pCoreOf 2 K)
    {k : G} (hkK : k ∈ K) (hkH : k ∈ H)
    (hcent : ∀ w ∈ subM V₁ (conjClosure I H) I,
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          (⟨k, hkH⟩⁻¹ * ⟨t, hF.T_le_H ht⟩) w * w⁻¹ ∈
        subM V₁ (conjClosure I H) I ⊓
          fixV (autIH V₁ I H (conjClosure K T))) : False := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I))
        (autIH V₁ I H T) := hirrT
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := fun s hs =>
    Subgroup.mem_normalizer_fintype fun k' hk' => by
      have := mem_conjClosure hs hk'
      rwa [hK₀] at this
  have hkt : k⁻¹ * t ∈ Subgroup.normalizer (I : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKI' hkK)) (hTI ht)
  have hkN : k⁻¹ * t ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hkK)) (hTK ht)
  obtain ⟨a, ha_def⟩ : ∃ a : ↥H, a = ⟨k, hkH⟩⁻¹ * ⟨t, hTH ht⟩ := ⟨_, rfl⟩
  have ha : actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) a ∈
      centSec (subM V₁ (conjClosure I H) I)
        (subM V₁ (conjClosure I H) I ⊓
          fixV (autIH V₁ I H (conjClosure K T))) := by
    subst ha_def
    refine ⟨?_, hcent⟩
    exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁ (hF.conjClosure_le_normalizer_V₁ hIU)
      (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) _).mpr hkt
  have hk1 : t⁻¹ * k * t ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (hTK (T.inv_mem ht)) k).mp hkK
    simpa using this
  obtain ⟨x', hx'K, hc⟩ := hout _ hk1
  have e : t * (t⁻¹ * k * t)⁻¹ = k⁻¹ * t := by group
  rw [e] at hc
  have hcK : k⁻¹ * t * x' * (k⁻¹ * t)⁻¹ * x'⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hkN x').mp hx'K) (K.inv_mem hx'K)
  apply hc
  refine mem_pCoreOf_of_centSec hF hK₀ hP hV₁I hIU hirrT hcK ?_
  have hb := actH_mem_stabSub_inf hF hK₀ hV₁I hIU (hKH hx'K) (hKI' hx'K)
    (Subgroup.le_normalizer hx'K)
  have hbV := (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
    (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
    (le_conjClosure I H) ⟨x', hKH hx'K⟩).mpr (hKI' hx'K)
  have e2 : (⟨_, hKH hcK⟩ : ↥H) = a * (⟨x', hKH hx'K⟩ * a⁻¹ * ⟨x', hKH hx'K⟩⁻¹) := by
    subst ha_def
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e2, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact Subgroup.mul_mem _ ha (L32A.C.conj_mem_centSec hbV hb (Subgroup.inv_mem _ ha))

theorem false_of_T_le_normalizer_I (hA21 : AsA21SQTKSection) (hSQ : SQTKGroup ↥H)
    (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K)
    (hP : IsPSL 3 2 1 (L32A.cStar K)) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirrT : IsIrrPlusTildeT hF hIU) (hTI : T ≤ Subgroup.normalizer (I : Set G)) {t : G}
    (ht : t ∈ T) (hout : ∀ k ∈ K, ∃ x ∈ K, t * k⁻¹ * x * (t * k⁻¹)⁻¹ * x⁻¹ ∉ pCoreOf 2 K) :
    False := by
  have := factElem hF hIU
  have hGL := autSec_eq_of_T_le hA21 hSQ hF hK₀ hP hV₁I hIU hirrT hTI
  obtain ⟨k, hkK, hkH, hcent⟩ := exists_centSec_of_autSec_eq hSQ hF hK₀ hV₁I hIU hirrT hTI hGL ht
  exact false_of_centSec hF hK₀ hP hV₁I hIU hirrT hTI ht hout hkK hkH hcent


theorem exists_cube_of_x (hF : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {x : G} (hxH : x ∈ H)
    (hx3 : x ^ 3 = 1)
    (hθ : ∀ u ∈ conjClosure Vp H, u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹) ∈ V₁)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    ∃ y : MulAut ↥(tildeOf V₁ (conjClosure I H)), y ^ 3 = 1 ∧
      (∀ w, w * y w * y (y w) = 1) ∧ ∀ γ ∈ autIH V₁ I H K, γ * y = y * γ := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIH := le_normalizer_conjClosure I H
  set ψ := actH hF.H_le_normalizer_V₁ hIH with hψ
  refine ⟨ψ ⟨x, hxH⟩, ?_, ?_, ?_⟩
  · have h1 : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [← map_pow, h1, map_one]
  · intro w
    obtain ⟨a, haI, haw⟩ := exists_mk_of_mem_tilde w
    have hwa : w = modMk hIHN (a : G) haI := Subtype.ext haw.symm
    have h1 := (Subgroup.mem_normalizer_iff.mp (hIH hxH) _).mp haI
    have h2 := (Subgroup.mem_normalizer_iff.mp (hIH hxH) _).mp h1
    have hθa := hθ (a : G) (hIHU haI)
    rw [hwa, actH_modMk hF.H_le_normalizer_V₁ hIHN hIH ⟨x, hxH⟩ haI,
      actH_modMk hF.H_le_normalizer_V₁ hIHN hIH ⟨x, hxH⟩ h1]
    apply Subtype.ext
    show secMk _ _ ⟨(a : G), _⟩ * secMk _ _ ⟨x * a * x⁻¹, _⟩ *
      secMk _ _ ⟨x * (x * a * x⁻¹) * x⁻¹, _⟩ = 1
    rw [← map_mul, ← map_mul]
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (V₁ : Set G))
      (B := V₁) (x := ⟨_, hIHN ((conjClosure I H).mul_mem
        ((conjClosure I H).mul_mem haI h1) h2)⟩)).mpr hθa
  · intro γ hγ
    rw [autIH_eq_map hF hKH] at hγ
    obtain ⟨k, hk, rfl⟩ := hγ
    have hc := hxK k (Subgroup.mem_subgroupOf.mp hk)
    have h0 := hF.actH_eq_one_of_mem_pCoreOf hIU
      (x := ⟨x * (k : G) * x⁻¹ * (k : G)⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hxH k.2)
        (H.inv_mem hxH)) (H.inv_mem k.2)⟩) hc
    have e0 : (⟨x * (k : G) * x⁻¹ * (k : G)⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hxH k.2)
        (H.inv_mem hxH)) (H.inv_mem k.2)⟩ : ↥H) = ⟨x, hxH⟩ * k * ⟨x, hxH⟩⁻¹ * k⁻¹ := rfl
    have h1 : ψ (⟨x, hxH⟩ * k * ⟨x, hxH⟩⁻¹ * k⁻¹) = 1 := by
      rw [← e0]
      exact h0
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have e : ψ k * ψ ⟨x, hxH⟩ =
        (ψ ⟨x, hxH⟩ * ψ k * (ψ ⟨x, hxH⟩)⁻¹ * (ψ k)⁻¹)⁻¹ * (ψ ⟨x, hxH⟩ * ψ k) := by group
    rw [e, h1, inv_one, one_mul]

theorem false_of_d310Two (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hP : IsPSL 3 2 1 (L32A.cStar K)) {x : G} (hxH : x ∈ H)
    (hx3 : x ^ 3 = 1)
    (hθ : ∀ u ∈ conjClosure Vp H, u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹) ∈ V₁)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirrT : IsIrrPlusTildeT hF hIU)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h3 : D310Two (autIH V₁ I H T) (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) : False := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirrT
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK₀]
  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := slThree_isSimple
  have hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    ((L32A.C.cStarEquiv K).symm.trans φ).isSimpleGroup
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨e3⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS' hne
  have hcard : Nat.card ↥(autIH V₁ I H K) = 168 := by
    rw [← Nat.card_congr e3.toEquiv, Nat.card_congr ((L32A.C.cStarEquiv K).symm.trans φ).toEquiv,
      L32A.C.card_sl32]
  have h8 := L32A.C.relIndex_eq_eight_of_d310Two h3 hcard
  obtain ⟨y, hy3, hcube, hyL⟩ := exists_cube_of_x hF hIU hxH hx3 hθ hxK
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := fun s hs =>
    Subgroup.mem_normalizer_fintype fun k' hk' => by
      have := mem_conjClosure hs hk'
      rwa [hK₀] at this
  have hTL : ∀ s ∈ autIH V₁ I H T, ∀ γ ∈ autIH V₁ I H K, s * γ * s⁻¹ ∈ autIH V₁ I H K := by
    intro s hs γ hγ
    rw [autIH_eq_map hF hTH] at hs
    rw [autIH_eq_map hF hKH] at hγ ⊢
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨k, hk, rfl⟩ := hγ
    refine ⟨t * k * t⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hTK (Subgroup.mem_subgroupOf.mp ht)) _).mp
      (Subgroup.mem_subgroupOf.mp hk)
  have hTL' : ∀ s ∈ autIH V₁ I H T, ∀ γ ∈ autIH V₁ I H K, s⁻¹ * γ * s ∈ autIH V₁ I H K := by
    intro s hs γ hγ
    have h1 := hTL s⁻¹ ((autIH V₁ I H T).inv_mem hs) γ hγ
    simpa using h1
  have hW : ∀ w : ↥(tildeOf V₁ (conjClosure I H)), w * w = 1 := by
    intro w
    apply Subtype.ext
    have := (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))).2 w w.2
    simpa [pow_two] using this
  exact L32A.C.false_of_d310Two_of_cube hW hMp hirr'.1.2.2.2
    (autIH_le_stabSub_of hF hIU hV₁I hKH hKI') hTL hTL' h3 h8 hy3 hcube hyL

theorem mem_stabSub_of_eq_orbSup_T {W : Type} [CommGroup W] {T : Subgroup (MulAut W)}
    {U : Subgroup W} (h : U = orbSup T U) {t : MulAut W} (ht : t ∈ T) :
    t ∈ CFSG.Quasithin.stabSub U :=
  CFSG.Quasithin.H13.A6.A6M22.mem_stabSub_of_eq_orbSup h ht

theorem false_of_outer (hA21 : AsA21SQTKSection) (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (hSQ : SQTKGroup ↥H) (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K)
    (hP : IsPSL 3 2 1 (L32A.cStar K)) {x : G} (hxH : x ∈ H) (hx3 : x ^ 3 = 1)
    (hθ : ∀ u ∈ conjClosure Vp H, u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹) ∈ V₁)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) {t : G} (ht : t ∈ T)
    (hout : ∀ k ∈ K, ∃ x ∈ K, t * k⁻¹ * x * (t * k⁻¹)⁻¹ * x⁻¹ ∉ pCoreOf 2 K) : False := by
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirrT := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have := factElem hF hIU
  have h4 := (F918_4' hF hSQ hK₀ hV₁I hIU W hW hirrU hD310 hD391 hI4).2
  rcases h4 with hHI | (⟨hVT, -⟩ | h3)
  ·
    exact false_of_T_le_normalizer_I hA21 hSQ hF hK₀ hP hV₁I hIU hirrT
      (hF.T_le_H.trans hHI) ht hout
  ·
    have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
      intro t' ht'
      have hst := mem_stabSub_of_eq_orbSup_T hVT
        (actH_mem_autIH_of_mem (I := I) hF hF.T_le_H ht')
      exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
        (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
        (le_conjClosure I H) ⟨t', hF.T_le_H ht'⟩).mp hst
    exact false_of_T_le_normalizer_I hA21 hSQ hF hK₀ hP hV₁I hIU hirrT hTI ht hout
  ·
    exact false_of_d310Two hF hK₀ hP hxH hx3 hθ hxK hV₁I hIU hirrT h3

end CFSG.Quasithin.H13.A6.A6L32
