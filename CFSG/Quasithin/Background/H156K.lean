module

public import CFSG.Quasithin.Background.H158KT
public import CFSG.Quasithin.Background.H158UTrio

public section

namespace CFSG.Quasithin.H156

open CFSG.Quasithin.H158U CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Quasithin CFSG.Open

theorem conj_apply_fix {V : Type*} [CommGroup V] (a b : MulAut V) (u : V)
    (h : b (a⁻¹ u) = a⁻¹ u) : (a * b * a⁻¹ : MulAut V) u = u := by
  have h2 : (a * b * a⁻¹ : MulAut V) u = a (b (a⁻¹ u)) := rfl
  rw [h2, h]
  exact MulAut.apply_inv_self V a u

@[expose] noncomputable def Kperm : Subgroup (Equiv.Perm (Fin 24)) :=
  ((img11 trQ ⊓ centSub UT).comap rhoM24).map AutPerm.subtype

theorem mem_Kperm {σ : Equiv.Perm (Fin 24)} :
    σ ∈ Kperm ↔ ∃ h : σ ∈ AutPerm, rhoM24 ⟨σ, h⟩ ∈ img11 trQ ⊓ centSub UT := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨σ, h⟩, hx, rfl⟩

theorem Kperm_le_aut : Kperm ≤ AutPerm := fun _ hσ => (mem_Kperm.1 hσ).1

theorem card_img11 {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (hΓ : Γ ≤ AutPerm) : Nat.card ↥(img11 Γ) = Nat.card ↥Γ := by
  rw [img11, Subgroup.card_map_of_injective (rho11_injective AutPerm le_rfl),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΓ).toEquiv]

theorem img11_Kperm : img11 Kperm = img11 trQ ⊓ centSub UT := by
  have hsub : Kperm.subgroupOf AutPerm = (img11 trQ ⊓ centSub UT).comap rhoM24 :=
    Subgroup.comap_map_eq_self_of_injective AutPerm.subtype_injective _
  rw [img11, hsub]
  refine Subgroup.map_comap_eq_self ?_
  rw [range_rho11_eq_img11 AutPerm le_rfl]
  exact inf_le_left.trans (img11_trQ_le.trans inf_le_left)

theorem Kperm_le_trQ : Kperm ≤ trQ := by
  intro σ hσ
  obtain ⟨h, hx⟩ := mem_Kperm.1 hσ
  obtain ⟨y, hy, hyx⟩ := hx.1
  have : y = ⟨σ, h⟩ := rho11_injective AutPerm le_rfl hyx
  rw [this] at hy
  exact Subgroup.mem_subgroupOf.1 hy

theorem stabUTP_eq_genT :
    genT = stabUTP := by
  obtain ⟨hcS, hSP, hQc⟩ := CFSG.Quasithin.H158U.stab_facts
  have h1 : 6 * Nat.card ↥trQ ≤ Nat.card ↥genT :=
    mul_card_le_of_cosets trQ_le_genT twP tw_mem_genT
      fun i j h => tw_distinct i j (trQ_le_trioP0 h)
  exact Subgroup.eq_of_le_of_card_ge (genT_le.trans inf_le_left) (by omega)

theorem trQ_eq_inf :
    trQ = trioP0 ⊓ stabUTP := by
  obtain ⟨hcS, hSP, hQc⟩ := CFSG.Quasithin.H158U.stab_facts
  have heq := stabUTP_eq_genT
  have h2 : 6 * Nat.card ↥(trioP0 ⊓ stabUTP) ≤ Nat.card ↥stabUTP :=
    mul_card_le_of_cosets inf_le_right twP (fun i => heq ▸ tw_mem_genT i)
      fun i j h => tw_distinct i j h.1
  have hQle : trQ ≤ trioP0 ⊓ stabUTP := le_inf trQ_le_trioP0 trQ_le_stabUTP
  exact Subgroup.eq_of_le_of_card_ge hQle (by omega)

theorem rho_stabUTP_mem_stabSub {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ stabUTP) (h : σ ∈ AutPerm) :
    rhoM24 ⟨σ, h⟩ ∈ stabSub UT := by
  obtain ⟨x, hx, rfl⟩ := hσ
  exact hx

theorem perfectCore_stabUTP' :
    perfectCore stabUTP = trQ := by
  obtain ⟨hcS, hSP, hQc⟩ := CFSG.Quasithin.H158U.stab_facts
  exact (perfectCore_stabUTP hcS.le (by omega)).1

set_option maxRecDepth 20000 in
theorem Kperm_conj
    {s k : Equiv.Perm (Fin 24)} (hs : s ∈ stabUTP) (hk : k ∈ Kperm) : s * k * s⁻¹ ∈ Kperm := by
  have hsA : s ∈ AutPerm := stabUTP_le_autPerm hs
  have hkQ : k ∈ trQ := Kperm_le_trQ hk
  obtain ⟨hkA, hkc⟩ := mem_Kperm.1 hk
  have hkP : k ∈ perfectCore stabUTP := by rw [perfectCore_stabUTP']; exact hkQ
  have hconj : s * k * s⁻¹ ∈ perfectCore stabUTP := by
    have := (perfectCore_normal stabUTP).conj_mem ⟨k, perfectCore_le _ hkP⟩
      (Subgroup.mem_subgroupOf.2 hkP) ⟨s, hs⟩
    exact Subgroup.mem_subgroupOf.1 this
  rw [perfectCore_stabUTP'] at hconj
  have hA : s * k * s⁻¹ ∈ AutPerm :=
    AutPerm.mul_mem (AutPerm.mul_mem hsA hkA) (AutPerm.inv_mem hsA)
  refine mem_Kperm.2 ⟨hA, ?_, ?_⟩
  · refine ⟨⟨s * k * s⁻¹, hA⟩, Subgroup.mem_subgroupOf.2 hconj, rfl⟩
  · have e0 : (⟨s * k * s⁻¹, hA⟩ : ↥AutPerm) = ⟨s, hsA⟩ * ⟨k, hkA⟩ * ⟨s, hsA⟩⁻¹ := by
      apply Subtype.ext
      simp
    have e : rhoM24 ⟨s * k * s⁻¹, hA⟩ =
        rhoM24 ⟨s, hsA⟩ * rhoM24 ⟨k, hkA⟩ * (rhoM24 ⟨s, hsA⟩)⁻¹ := by
      rw [e0, map_mul, map_mul, map_inv]
    have hsS := rho_stabUTP_mem_stabSub hs hsA
    intro u hu
    have h1 : (rhoM24 ⟨s, hsA⟩)⁻¹ u ∈ UT := (mem_stabSub.1 (Subgroup.inv_mem _ hsS) u).2 hu
    rw [e]
    exact conj_apply_fix (rhoM24 ⟨s, hsA⟩) (rhoM24 ⟨k, hkA⟩) u (hkc.2 _ h1)

theorem card_Kperm :
    Nat.card ↥Kperm = 64 := by
  have h := card_img11 Kperm_le_aut
  rw [img11_Kperm] at h
  rw [← h]
  exact card_ktCent

theorem Kperm_le_stab : Kperm ≤ stabUTP :=
  Kperm_le_trQ.trans trQ_le_stabUTP

theorem Kperm_normal :
    (Kperm.subgroupOf stabUTP).Normal :=
  ⟨fun n hn g => Subgroup.mem_subgroupOf.2
    (Kperm_conj g.2 (Subgroup.mem_subgroupOf.1 hn))⟩

theorem Kperm_le_pCoreOf :
    Kperm ≤ pCoreOf 2 stabUTP := by
  have hle : Kperm ≤ stabUTP := Kperm_le_stab
  have hN := Kperm_normal
  have hP : IsPGroup 2 ↥(Kperm.subgroupOf stabUTP) := by
    have : Nat.card ↥(Kperm.subgroupOf stabUTP) = 2 ^ 6 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_Kperm]
      norm_num
    exact IsPGroup.of_card this
  have hcore : Kperm.subgroupOf stabUTP ≤ CFSG.pCore 2 ↥stabUTP := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le _ (le_iSup_of_le hN (le_iSup_of_le hP le_rfl))
  have := Subgroup.map_mono (f := stabUTP.subtype) hcore
  rw [Subgroup.map_subgroupOf_eq_of_le hle] at this
  exact this

theorem s3_key : ∀ x : Equiv.Perm (Fin 3), (∀ c : Equiv.Perm (Fin 3), (x * (c * x * c⁻¹)) ^ 2 = 1) →
    x = 1 := by
  decide +kernel

theorem s3_normal_two_trivial (N : Subgroup (Equiv.Perm (Fin 3))) [hN : N.Normal]
    (hP : IsPGroup 2 ↥N) : N = ⊥ := by
  have hsq : ∀ x ∈ N, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have hk' : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf x ∣ 6 := by
      have := orderOf_dvd_natCard x
      rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
    obtain ⟨j, -, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hj : j ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have h4 : 2 ^ 2 ∣ orderOf x := hjo ▸ (pow_dvd_pow 2 hcon)
      have := h4.trans h2
      omega
    have : orderOf x ∣ 2 := by
      rw [hjo]
      exact (pow_dvd_pow 2 hj).trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.1 this
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  refine s3_key x fun c => hsq _ (N.mul_mem hx (hN.conj_mem x hx c))

@[expose] noncomputable def trioHom (hSP : stabUTP ≤ trioP) : ↥stabUTP →* Equiv.Perm (Fin 3) :=
  (blockHom (lab := lab) (rep := trRep) lab_trRep).comp (Subgroup.inclusion hSP)

theorem trioHom_eq_one_iff (hSP : stabUTP ≤ trioP) (σ : ↥stabUTP) :
    trioHom hSP σ = 1 ↔ (σ : Equiv.Perm (Fin 24)) ∈ trioP0 := by
  have hσ : (σ : Equiv.Perm (Fin 24)) ∈ trioP := hSP σ.2
  constructor
  · intro h x
    have h1 : ∀ i, lab ((σ : Equiv.Perm (Fin 24)) (trRep i)) = i := fun i => by
      have := congrArg (fun π : Equiv.Perm (Fin 3) => π i) h
      exact this
    rw [blockFun_lab lab_trRep hσ x]
    exact h1 (lab x)
  · intro h
    refine Equiv.ext fun i => ?_
    show lab ((σ : Equiv.Perm (Fin 24)) (trRep i)) = i
    rw [h (trRep i), lab_trRep]

theorem trioHom_surjective
    (hSP : stabUTP ≤ trioP) :
    Function.Surjective (trioHom hSP) := by
  have heq := stabUTP_eq_genT
  have hmem : ∀ i : Fin 6, twP i ∈ stabUTP := fun i => heq ▸ tw_mem_genT i
  have hinj : Function.Injective fun i : Fin 6 => trioHom hSP ⟨twP i, hmem i⟩ := by
    intro i j hij
    apply tw_distinct i j
    have h1 : trioHom hSP ((⟨twP i, hmem i⟩ : ↥stabUTP)⁻¹ * ⟨twP j, hmem j⟩) = 1 := by
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.2 hij
    exact (trioHom_eq_one_iff hSP _).1 h1
  have hbij : Function.Bijective fun i : Fin 6 => trioHom hSP ⟨twP i, hmem i⟩ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [Fintype.card_perm, Nat.factorial]⟩
  intro π
  obtain ⟨i, hi⟩ := hbij.2 π
  exact ⟨⟨twP i, hmem i⟩, hi⟩

theorem pCoreOf_le_trQ :
    pCoreOf 2 stabUTP ≤ trQ := by
  obtain ⟨-, hSP, -⟩ := CFSG.Quasithin.H158U.stab_facts
  have hQn : (CFSG.pCore 2 ↥stabUTP).Normal := CFSG.pCore_normal
  have hQp : IsPGroup 2 ↥(CFSG.pCore 2 ↥stabUTP) := CFSG.pCore_isPGroup
  have hN : ((CFSG.pCore 2 ↥stabUTP).map (trioHom hSP)).Normal :=
    hQn.map _ (trioHom_surjective hSP)
  have hP : IsPGroup 2 ↥((CFSG.pCore 2 ↥stabUTP).map (trioHom hSP)) := hQp.map _
  have hbot := s3_normal_two_trivial _ hP
  rintro σ ⟨q, hq, rfl⟩
  have h1 : trioHom hSP q = 1 := by
    have : trioHom hSP q ∈ (CFSG.pCore 2 ↥stabUTP).map (trioHom hSP) := ⟨q, hq, rfl⟩
    rw [hbot] at this
    exact this
  rw [trQ_eq_inf]
  exact ⟨(trioHom_eq_one_iff hSP q).1 h1, q.2⟩

section Generic

variable {V : Type*} [CommGroup V] (U : Subgroup V) {K : Type*} [Group K] (f : K →* MulAut V)
  (X : Subgroup (MulAut V)) (hfX : ∀ k, f k ∈ X) (hf : ∀ k, f k ∈ stabSub U)

@[expose] def actHom : K →* ↥(autSub X U) :=
  ((resHom U).comp (f.codRestrict (stabSub U) hf)).codRestrict _
    fun k => mem_autSub.2 ⟨⟨f k, hf k⟩, hfX k, rfl⟩

include hfX hf in
theorem actHom_surjective (hsurj : ∀ x ∈ X, ∃ k, f k = x) :
    Function.Surjective (actHom U f X hfX hf) := by
  intro φ
  obtain ⟨g, hg, hgφ⟩ := mem_autSub.1 φ.2
  obtain ⟨k, hk⟩ := hsurj _ hg
  refine ⟨k, Subtype.ext ?_⟩
  show resHom U ⟨f k, hf k⟩ = _
  rw [← hgφ]
  congr 1
  exact Subtype.ext hk

include hfX hf in
theorem actHom_eq_one_iff (k : K) : actHom U f X hfX hf k = 1 ↔ f k ∈ centSub U := by
  have h1 : actHom U f X hfX hf k = 1 ↔ resHom U ⟨f k, hf k⟩ = 1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [h1, ← MonoidHom.mem_ker, ker_resHom, Subgroup.mem_subgroupOf]

end Generic

theorem img11_trQ_stab : img11 trQ ≤ stabSub UT := img11_trQ_le.trans inf_le_right

theorem rho_trQ_mem {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ trQ) :
    rhoM24 ⟨σ, trQ_le hσ⟩ ∈ img11 trQ :=
  ⟨⟨σ, trQ_le hσ⟩, Subgroup.mem_subgroupOf.2 hσ, rfl⟩

@[expose] noncomputable def fTrQ : ↥trQ →* MulAut W11 := rhoM24.comp (Subgroup.inclusion trQ_le)

theorem fTrQ_apply (σ : ↥trQ) : fTrQ σ = rhoM24 ⟨σ.1, trQ_le σ.2⟩ := rfl

theorem fTrQ_mem (σ : ↥trQ) : fTrQ σ ∈ img11 trQ := rho_trQ_mem σ.2

theorem fTrQ_stab (σ : ↥trQ) : fTrQ σ ∈ stabSub UT := img11_trQ_stab (fTrQ_mem σ)

theorem fTrQ_surj : ∀ x ∈ img11 trQ, ∃ k : ↥trQ, fTrQ k = x := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩

@[expose] noncomputable def thetaHom : ↥trQ →* ↥(autSub (img11 trQ) UT) :=
  actHom UT fTrQ (img11 trQ) fTrQ_mem fTrQ_stab

theorem thetaHom_surjective : Function.Surjective thetaHom :=
  actHom_surjective UT fTrQ (img11 trQ) fTrQ_mem fTrQ_stab fTrQ_surj

theorem thetaHom_eq_one_iff (σ : ↥trQ) :
    thetaHom σ = 1 ↔ fTrQ σ ∈ centSub UT :=
  actHom_eq_one_iff UT fTrQ (img11 trQ) fTrQ_mem fTrQ_stab σ

theorem card_autSub_trQ :
    Nat.card ↥(autSub (img11 trQ) UT) = 168 := by
  obtain ⟨-, -, hQc⟩ := CFSG.Quasithin.H158U.stab_facts
  have h := card_autSub_mul (A := img11 trQ) (U := UT) img11_trQ_stab
  have hk : Nat.card ↥(img11 trQ ⊓ centSub UT) = 64 := card_ktCent
  have hc : Nat.card ↥(img11 trQ) = 10752 := (card_img11 trQ_le).trans hQc
  have h2 : Nat.card ↥(autSub (img11 trQ) UT) * 64 = Nat.card ↥(img11 trQ) := by
    rw [← hk]
    exact h
  omega

theorem pCoreOf_cent
    {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ pCoreOf 2 stabUTP) (hA : σ ∈ AutPerm) :
    rhoM24 ⟨σ, hA⟩ ∈ centSub UT := by
  haveI : IsSimpleGroup ↥(autSub (img11 trQ) UT) := (lu_coc_std card_stab_UT_le).2.2.1
  have hQle : pCoreOf 2 stabUTP ≤ trQ := pCoreOf_le_trQ
  have hQp : IsPGroup 2 ↥(pCoreOf 2 stabUTP) := CFSG.pCore_isPGroup.map _
  let Qt : Subgroup ↥trQ := (pCoreOf 2 stabUTP).subgroupOf trQ
  have hQtn : Qt.Normal := ⟨fun n hn g => by
    obtain ⟨q, hq, hqn⟩ := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ⟨⟨g.1, trQ_le_stabUTP g.2⟩ * q *
      ⟨g.1, trQ_le_stabUTP g.2⟩⁻¹, CFSG.pCore_normal.conj_mem q hq _, ?_⟩
    simp [← hqn]⟩
  have hQtp : IsPGroup 2 ↥Qt :=
    hQp.of_injective (Subgroup.subgroupOfEquivOfLe hQle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQle).injective
  have hN : (Qt.map thetaHom).Normal := hQtn.map _ thetaHom_surjective
  have hP : IsPGroup 2 ↥(Qt.map thetaHom) := hQtp.map _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Qt.map thetaHom) with h0 | h1
  · have : thetaHom ⟨σ, hQle hσ⟩ ∈ Qt.map thetaHom :=
      ⟨⟨σ, hQle hσ⟩, Subgroup.mem_subgroupOf.2 hσ, rfl⟩
    rw [h0] at this
    have h2 := (thetaHom_eq_one_iff ⟨σ, hQle hσ⟩).1 this
    rwa [fTrQ_apply] at h2
  · exfalso
    rw [h1] at hP
    have hX : IsPGroup 2 ↥(autSub (img11 trQ) UT) := hP.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hX
    rw [card_autSub_trQ] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 168)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem pCoreOf_stabUTP :
    pCoreOf 2 stabUTP = Kperm := by
  refine le_antisymm (fun σ hσ => ?_) Kperm_le_pCoreOf
  have hQ : σ ∈ trQ := pCoreOf_le_trQ hσ
  have hA : σ ∈ AutPerm := trQ_le hQ
  exact mem_Kperm.2 ⟨hA, ⟨⟨σ, hA⟩, Subgroup.mem_subgroupOf.2 hQ, rfl⟩, pCoreOf_cent hσ hA⟩

end CFSG.Quasithin.H156
