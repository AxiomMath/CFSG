module

public import CFSG.Quasithin.H13.L32AC47j
public import CFSG.Quasithin.H13.L32AC47c
public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge
public import CFSG.Quasithin.EmptyFaithful.LRed14B45
public import CFSG.Quasithin.EmptyFaithful.F918C5
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.SmithB45SL3L32
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Vol2Native.A312L.Seven

attribute [local instance] commGroupOfFact

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  rw [h, Subgroup.mem_bot] at hez
  exact Subgroup.mem_bot.mpr (e.injective (hez.trans (map_one e).symm))

theorem conj_mem_centSec {W : Type*} [CommGroup W] {U D : Subgroup W} {g c : MulAut W}
    (hgU : g ∈ stabSub U) (hgD : g ∈ stabSub D) (hc : c ∈ centSec U D) :
    g * c * g⁻¹ ∈ centSec U D :=
  CFSG.Quasithin.StabLat.conj_mem_centSec hgU hgD hc

theorem mem_stabSub_fixV_of_conj {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)}
    {a : MulAut W} (h1 : ∀ m ∈ X, a * m * a⁻¹ ∈ X) (h2 : ∀ m ∈ X, a⁻¹ * m * a ∈ X) :
    a ∈ stabSub (fixV X) := by
  intro u
  constructor
  · intro hu m hm
    have h3 := hu _ (h1 m hm)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h3
    exact a.injective h3
  · intro hu m hm
    have h3 := hu _ (h2 m hm)
    rw [MulAut.mul_apply, MulAut.mul_apply] at h3
    have h4 := congrArg a h3
    rwa [MulAut.apply_inv_self] at h4

theorem mem_stabSub_inf {W : Type*} [CommGroup W] {A B : Subgroup W} {g : MulAut W}
    (hA : g ∈ stabSub A) (hB : g ∈ stabSub B) : g ∈ stabSub (A ⊓ B) := fun u =>
  ⟨fun h => ⟨(hA u).mp h.1, (hB u).mp h.2⟩, fun h => ⟨(hA u).mpr h.1, (hB u).mpr h.2⟩⟩

theorem inv_apply_mul_inv_mem_of_secHom_eq {V : Type*} [CommGroup V] {W U : Subgroup V}
    {X : Subgroup (MulAut V)} (hXW : X ≤ stabSub W) (hXU : X ≤ stabSub U) {a b : ↥X}
    (h : B5.secHom X hXW hXU a = B5.secHom X hXW hXU b) :
    ∀ w ∈ W, (a : MulAut V)⁻¹ ((b : MulAut V) w) * w⁻¹ ∈ U := by
  have hk : a⁻¹ * b ∈ (B5.secHom X hXW hXU).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  exact ((B5.mem_ker_secHom X hXW hXU _).mp hk).2

variable {G : Type} [Group G] [Finite G] {T L V H K I : Subgroup G}

theorem autIH_le_stabSub_of (hF : HypF918 T V L (fsuV1 T V) V H K) (hIU : I ≤ conjClosure V H)
    (hV₁I : fsuV1 T V ≤ I) [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]
    {X : Subgroup G} (hXH : X ≤ H) (hXI : X ≤ Subgroup.normalizer (I : Set G)) :
    autIH (fsuV1 T V) I H X ≤ stabSub (subM (fsuV1 T V) (conjClosure I H) I) := by
  intro g hg
  rw [autIH_eq_map hF hXH] at hg
  obtain ⟨s, hs, rfl⟩ := hg
  exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁ (hF.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) s).mpr
    (hXI (Subgroup.mem_subgroupOf.mp hs))

theorem autSec_eq_of_T_le (hA21 : AsA21SQTKSection) (S : Setting147 G T L V H)
    (hF : HypF918 T V L (fsuV1 T V) V H K) (hK₀ : conjClosure K T = K)
    (hP : IsPSL 3 2 1 (cStar K)) (hV₁I : fsuV1 T V ≤ I) (hIU : I ≤ conjClosure V H)
    (hirrT : IsIrrPlusTildeT hF hIU) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))] :
    autSec (autSub (autIH (fsuV1 T V) I H (conjClosure K T) ⊔ autIH (fsuV1 T V) I H T)
        (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
      ((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I)) =
    autSec (autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
      ((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I)) := by
  classical
  have hSQ := sqtkGroup_of_setting S
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
  have hD3 : D3Std (autIH (fsuV1 T V) I H H) (autIH (fsuV1 T V) I H (conjClosure K T))
      (autIH (fsuV1 T V) I H T) (autIH (fsuV1 T V) I H K)
      (subM (fsuV1 T V) (conjClosure I H) I) := ⟨hD, hA.qhat_VT hD.exp, hirr'⟩
  have hMp : autIH (fsuV1 T V) I H (conjClosure K T) = autIH (fsuV1 T V) I H K := by rw [hK₀]
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hT := autIH_le_stabSub_of hF hIU hV₁I hF.T_le_H hTI
  have hLs := autIH_le_stabSub_of hF hIU hV₁I hKH hKI'
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD hT
  have hQS := lred3_qsec hD hMp hO2
  have hB4 := lred3_b4Hyp hA21 hD hMp hO2
  have hqh := lred3_qhatOf_autSec hD3 hMp hT
  obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := slThree_isSimple
  have hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := ((cStarEquiv K).symm.trans φ).isSimpleGroup
  have hne : autIH (fsuV1 T V) I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨e3⟩ := nonempty_mulEquiv_quotient_autI hF hIU hS' hne
  have hL'S : IsSimpleGroup ↥(autIH (fsuV1 T V) I H K) := e3.symm.isSimpleGroup
  have hLnc : ¬ autIH (fsuV1 T V) I H K ≤ centSub (subM (fsuV1 T V) (conjClosure I H) I) := by
    intro hle
    apply ne_of_lt hirr'.1.2.2.2.1
    ext w
    constructor
    · exact fun h => h.1
    · intro hw
      refine ⟨hw, fun a => ?_⟩
      have ha : (a : MulAut _) ∈ autIH (fsuV1 T V) I H K := hMp ▸ a.2
      exact hle ha w hw
  have hfaith := inf_centSub_eq_bot_of_isSimpleGroup hL'S hLs hLnc
  let e2 := autSubEquivOfFaithful hLs hfaith
  let e1 := B5.secEquiv _ (InternalSec.le_stabSub_top _) hQS.stabKC hQS.faithful
  let eLs := e1.symm.trans (e2.symm.trans (e3.symm.trans ((cStarEquiv K).symm.trans φ)))
  have hZ := center_eq_bot_of_mulEquiv eLs sl3_center_eq_bot
  have hType : B42TypeL32 _ :=
    ⟨hZ, isPSL_three_two_iff.mpr ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans eLs)⟩⟩
  obtain ⟨eL⟩ := B42L2.exists_gl32_of_model hZ hType.2
  have hexp : ∀ v : Sec (⊤ : Subgroup ↥(subM (fsuV1 T V) (conjClosure I H) I))
      ((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I)), v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_pow]
      have h2 : w ^ 2 = 1 := Subtype.ext (Subtype.ext (by simp [hD.exp]))
      rw [h2, QuotientGroup.mk_one]
  have hS2 : ∀ v : Sec (⊤ : Subgroup ↥(subM (fsuV1 T V) (conjClosure I H) I))
      ((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I)), v * v = 1 := fun v => by
    rw [← pow_two]
    exact hexp v
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hS2
  have hq1 := asB45L32_holds _ hexp _ _ hB4 hType hqh
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender (isFFModule_of_qhatOf_le_one hexp hq1)
  exact B42L2.eq_of_l32 θ hB4 hZ eL hA

theorem qsec_of_T_le (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hK₀ : conjClosure K T = K) (hV₁I : fsuV1 T V ≤ I) (hIU : I ≤ conjClosure V H)
    (hirrT : IsIrrPlusTildeT hF hIU) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))] :
    InternalSec.QSec
      (autSub (autIH (fsuV1 T V) I H (conjClosure K T) ⊔ autIH (fsuV1 T V) I H T)
        (subM (fsuV1 T V) (conjClosure I H) I))
      (autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I))
      ((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I)) := by
  have hSQ := sqtkGroup_of_setting S
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hMp : autIH (fsuV1 T V) I H (conjClosure K T) = autIH (fsuV1 T V) I H K := by rw [hK₀]
  have hT := autIH_le_stabSub_of hF hIU hV₁I hF.T_le_H hTI
  exact lred3_qsec hD hMp (lred3_pCoreOf_autSub_sup_eq_bot hD hT)

theorem exists_centSec_of_autSec_eq (S : Setting147 G T L V H)
    (hF : HypF918 T V L (fsuV1 T V) V H K) (hK₀ : conjClosure K T = K) (hV₁I : fsuV1 T V ≤ I)
    (hIU : I ≤ conjClosure V H) (hirrT : IsIrrPlusTildeT hF hIU)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))]
    (hGL : autSec (autSub (autIH (fsuV1 T V) I H (conjClosure K T) ⊔ autIH (fsuV1 T V) I H T)
        (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
      ((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I)) =
    autSec (autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
      ((subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
          (subM (fsuV1 T V) (conjClosure I H) I)))
    {t : G} (ht : t ∈ T) :
    ∃ k ∈ K, ∃ hk : k ∈ H, ∀ w ∈ subM (fsuV1 T V) (conjClosure I H) I,
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          (⟨k, hk⟩⁻¹ * ⟨t, hF.T_le_H ht⟩) w * w⁻¹ ∈
        subM (fsuV1 T V) (conjClosure I H) I ⊓ fixV (autIH (fsuV1 T V) I H (conjClosure K T)) := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hT := autIH_le_stabSub_of hF hIU hV₁I hTH hTI
  have hQS := qsec_of_T_le S hF hK₀ hV₁I hIU hirrT hTI
  set ψ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hψ
  have hψt : ψ ⟨t, hTH ht⟩ ∈ autIH (fsuV1 T V) I H T := actH_mem_autIH_of_mem hF hTH ht
  obtain ⟨τ, hτ⟩ : ∃ τ : MulAut ↥(subM (fsuV1 T V) (conjClosure I H) I),
      τ = resHom _ ⟨ψ ⟨t, hTH ht⟩, hT hψt⟩ := ⟨_, rfl⟩
  have hτΛ : τ ∈ autSub (autIH (fsuV1 T V) I H (conjClosure K T) ⊔ autIH (fsuV1 T V) I H T)
      (subM (fsuV1 T V) (conjClosure I H) I) :=
    mem_autSub.mpr ⟨⟨ψ ⟨t, hTH ht⟩, hT hψt⟩, Subgroup.mem_sup_right hψt, hτ.symm⟩
  have hσt : B5.secHom _ (InternalSec.le_stabSub_top _) hQS.stab ⟨τ, hτΛ⟩ ∈
      autSec (autSub (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I)) ⊤
        ((subM (fsuV1 T V) (conjClosure I H) I ⊓
          fixV (autIH (fsuV1 T V) I H (conjClosure K T))).subgroupOf
            (subM (fsuV1 T V) (conjClosure I H) I)) := by
    rw [← hGL, ← B5.range_secHom _ (InternalSec.le_stabSub_top _) hQS.stab]
    exact ⟨_, rfl⟩
  rw [← B5.map_secHom_eq_autSec _ (InternalSec.le_stabSub_top _) hQS.stab hQS.le] at hσt
  obtain ⟨κ, hκK, hκσ⟩ := hσt
  have hker := inv_apply_mul_inv_mem_of_secHom_eq (InternalSec.le_stabSub_top _) hQS.stab hκσ
  obtain ⟨g, hgL, hgκ⟩ := mem_autSub.mp (Subgroup.mem_subgroupOf.mp hκK)
  have hgL' := hgL
  rw [autIH_eq_map hF hKH] at hgL'
  obtain ⟨⟨k, hkH⟩, hkK, hkg⟩ := hgL'
  refine ⟨k, Subgroup.mem_subgroupOf.mp hkK, hkH, fun w hw => ?_⟩
  have h1 := hker ⟨w, hw⟩ trivial
  subst hτ
  rw [← hgκ, Subgroup.mem_subgroupOf] at h1
  have h2 : (g : MulAut _)⁻¹ (ψ ⟨t, hTH ht⟩ w) * w⁻¹ ∈
      subM (fsuV1 T V) (conjClosure I H) I ⊓ fixV (autIH (fsuV1 T V) I H (conjClosure K T)) := h1
  rw [map_mul, map_inv, MulAut.mul_apply, hkg]
  exact h2

theorem actH_mem_stabSub_inf (hF : HypF918 T V L (fsuV1 T V) V H K) (hK₀ : conjClosure K T = K)
    (hV₁I : fsuV1 T V ≤ I) (hIU : I ≤ conjClosure V H)
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))] {h : G} (hh : h ∈ H)
    (hnI : h ∈ Subgroup.normalizer (I : Set G)) (hnK : h ∈ Subgroup.normalizer (K : Set G)) :
    actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨h, hh⟩ ∈
      stabSub (subM (fsuV1 T V) (conjClosure I H) I ⊓
        fixV (autIH (fsuV1 T V) I H (conjClosure K T))) := by
  have hMpK : autIH (fsuV1 T V) I H (conjClosure K T) =
      (K.subgroupOf H).map (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
    rw [autIH_eq_map hF hF.K₀_le_H, hK₀]
  refine mem_stabSub_inf ((actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
    (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
    (le_conjClosure I H) ⟨h, hh⟩).mpr hnI) (mem_stabSub_fixV_of_conj ?_ ?_)
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

theorem mem_pCoreOf_of_centSec (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hK₀ : conjClosure K T = K) (hP : IsPSL 3 2 1 (cStar K)) (hV₁I : fsuV1 T V ≤ I)
    (hIU : I ≤ conjClosure V H) (hirrT : IsIrrPlusTildeT hF hIU)
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))] {c : G} (hcK : c ∈ K)
    (hcc : actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
      ⟨c, le_of_mem_cComp hF.K_cComp hcK⟩ ∈ centSec (subM (fsuV1 T V) (conjClosure I H) I)
        (subM (fsuV1 T V) (conjClosure I H) I ⊓
          fixV (autIH (fsuV1 T V) I H (conjClosure K T)))) : c ∈ pCoreOf 2 K := by
  classical
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  set ψ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hψ
  set V' := subM (fsuV1 T V) (conjClosure I H) I with hV'
  set D := V' ⊓ fixV (autIH (fsuV1 T V) I H (conjClosure K T)) with hD
  have hirr' : V' ∈ IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
      (orbSup (autIH (fsuV1 T V) I H T) V') (autIH (fsuV1 T V) I H T) := hirrT
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hstab : ∀ h (hh : h ∈ H), h ∈ Subgroup.normalizer (I : Set G) →
      ψ ⟨h, hh⟩ ∈ stabSub V' := fun h hh hn =>
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
    exact conj_mem_centSec (hstab _ _ (hKI' g.2))
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
    have hMpK : autIH (fsuV1 T V) I H (conjClosure K T) = (K.subgroupOf H).map ψ := by
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

theorem false_of_centSec (hF : HypF918 T V L (fsuV1 T V) V H K) (hK₀ : conjClosure K T = K)
    (hP : IsPSL 3 2 1 (cStar K)) (hV₁I : fsuV1 T V ≤ I) (hIU : I ≤ conjClosure V H)
    (hirrT : IsIrrPlusTildeT hF hIU) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H)))] {t : G} (ht : t ∈ T)
    (hout : ∀ k ∈ K, ∃ x ∈ K, t * k⁻¹ * x * (t * k⁻¹)⁻¹ * x⁻¹ ∉ pCoreOf 2 K)
    {k : G} (hkK : k ∈ K) (hkH : k ∈ H)
    (hcent : ∀ w ∈ subM (fsuV1 T V) (conjClosure I H) I,
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
          (⟨k, hkH⟩⁻¹ * ⟨t, hF.T_le_H ht⟩) w * w⁻¹ ∈
        subM (fsuV1 T V) (conjClosure I H) I ⊓
          fixV (autIH (fsuV1 T V) I H (conjClosure K T))) : False := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
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
      centSec (subM (fsuV1 T V) (conjClosure I H) I)
        (subM (fsuV1 T V) (conjClosure I H) I ⊓
          fixV (autIH (fsuV1 T V) I H (conjClosure K T))) := by
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
  exact Subgroup.mul_mem _ ha (conj_mem_centSec hbV hb (Subgroup.inv_mem _ ha))

theorem false_of_T_le_normalizer_I (hA21 : AsA21SQTKSection) (S : Setting147 G T L V H)
    (hF : HypF918 T V L (fsuV1 T V) V H K) (hK₀ : conjClosure K T = K)
    (hP : IsPSL 3 2 1 (cStar K)) (hV₁I : fsuV1 T V ≤ I) (hIU : I ≤ conjClosure V H)
    (hirrT : IsIrrPlusTildeT hF hIU) (hTI : T ≤ Subgroup.normalizer (I : Set G)) {t : G}
    (ht : t ∈ T) (hout : ∀ k ∈ K, ∃ x ∈ K, t * k⁻¹ * x * (t * k⁻¹)⁻¹ * x⁻¹ ∉ pCoreOf 2 K) :
    False := by
  have := factElem hF hIU
  have hGL := autSec_eq_of_T_le hA21 S hF hK₀ hP hV₁I hIU hirrT hTI
  obtain ⟨k, hkK, hkH, hcent⟩ := exists_centSec_of_autSec_eq S hF hK₀ hV₁I hIU hirrT hTI hGL ht
  exact false_of_centSec hF hK₀ hP hV₁I hIU hirrT hTI ht hout hkK hkH hcent

end CFSG.Quasithin.H13.L32A.C
