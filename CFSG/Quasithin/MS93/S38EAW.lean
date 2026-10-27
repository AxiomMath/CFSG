module

public import CFSG.Quasithin.MS93.S38EAE6
public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.Quasithin.MS93.S38ESecMod

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin CFSG.Quasithin.MS93.S38E CFSG.Quasithin.B3
open scoped commutatorElement

variable {U₀ : Type} [Group U₀] {V G₀ Lt Tb Qa E : Subgroup U₀} {e : ℕ}
  (hS : EndSetup V G₀ Lt Tb Qa E e) (lam : ↥⁅V, V⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, V⁆, Tb⁆ → lam c = 1)

section WMod

abbrev WM : Type _ := Sec (commV (hS.kY lam hlam1)) (⊥ : Subgroup (hS.YM lam))

theorem isInv_botY : B3.IsInv (hS.rho lam hlam1) (⊥ : Subgroup (hS.YM lam)) := by
  intro g w hw
  rw [Subgroup.mem_bot] at hw ⊢
  rw [hw, map_one]

noncomputable abbrev wRho : ↥G₀ →* MulAut (WM hS lam hlam1) :=
  secAct (hS.rho lam hlam1) (hS.isInv_W0 lam hlam1) (isInv_botY hS lam hlam1)

noncomputable abbrev zW : Subgroup (WM hS lam hlam1) :=
  ((commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)).subgroupOf
    (commV (hS.kY lam hlam1))).map (QuotientGroup.mk' _)

noncomputable abbrev qWS : WM hS lam hlam1 →* hS.SM lam hlam1 :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    intro w hw
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hw
    rw [Subgroup.mem_comap, MonoidHom.id_apply, Subgroup.mem_subgroupOf, hw]
    exact Subgroup.one_mem _)

theorem qWS_mk (w : ↥(commV (hS.kY lam hlam1))) :
    qWS hS lam hlam1 (QuotientGroup.mk w) = QuotientGroup.mk w := rfl

theorem qWS_surjective : Function.Surjective (qWS hS lam hlam1) := by
  intro s
  induction s using QuotientGroup.induction_on with
  | H w => exact ⟨QuotientGroup.mk w, rfl⟩

theorem qWS_wRho (g : ↥G₀) (w : WM hS lam hlam1) :
    qWS hS lam hlam1 (wRho hS lam hlam1 g w) = hS.secRho lam hlam1 g (qWS hS lam hlam1 w) := by
  induction w using QuotientGroup.induction_on with
  | H w => rfl

theorem qWS_eq_one_iff (w : WM hS lam hlam1) : qWS hS lam hlam1 w = 1 ↔ w ∈ zW hS lam hlam1 := by
  induction w using QuotientGroup.induction_on with
  | H w =>
    rw [qWS_mk, QuotientGroup.eq_one_iff]
    constructor
    · intro hw
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w', hw', hww'⟩
      have : w' = w := by
        have h := QuotientGroup.eq.mp hww'
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h
        have h2 : (w' : hS.YM lam) = w := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
          exact inv_mul_eq_one.mp h
        exact Subtype.ext h2
      rw [← this]
      exact hw'

noncomputable abbrev iWY : WM hS lam hlam1 →* hS.YM lam :=
  QuotientGroup.lift _ (commV (hS.kY lam hlam1)).subtype (by
    intro w hw
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hw
    rw [MonoidHom.mem_ker, Subgroup.coe_subtype]
    exact hw)

theorem iWY_injective : Function.Injective (iWY hS lam hlam1) := by
  intro a b hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      have : a = b := Subtype.ext hab
      rw [this]

theorem iWY_wRho (g : ↥G₀) (w : WM hS lam hlam1) :
    iWY hS lam hlam1 (wRho hS lam hlam1 g w) = hS.rho lam hlam1 g (iWY hS lam hlam1 w) := by
  induction w using QuotientGroup.induction_on with
  | H w => rfl

instance finite_WM : Finite (WM hS lam hlam1) :=
  have : Finite (hS.YM lam) := hS.finite_YM lam
  inferInstance

theorem sq_WM (w : WM hS lam hlam1) : w ^ 2 = 1 := sec_sq (hS.sq_eq_one lam) w

noncomputable abbrev kW : Subgroup (MulAut (WM hS lam hlam1)) :=
  (Lt.subgroupOf G₀).map (wRho hS lam hlam1)

noncomputable abbrev eW : Subgroup (MulAut (WM hS lam hlam1)) :=
  (E.subgroupOf G₀).map (wRho hS lam hlam1)

theorem secRho_eq_one_of_wRho (g : ↥G₀) (hg : wRho hS lam hlam1 g = 1) :
    hS.secRho lam hlam1 g = 1 := by
  ext s
  obtain ⟨w, rfl⟩ := qWS_surjective hS lam hlam1 s
  rw [← qWS_wRho, hg]
  rfl

end WMod

section Cover

variable {Y' : Type*} [CommGroup Y']

theorem stab_commOn {K : Subgroup (MulAut Y')} {W : Subgroup Y'} (hW : Stab K W) :
    Stab K (G6.commOn K W) := by
  intro k hk x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k', hk', w, hw, rfl⟩ := hy
    have e : k (k' w * w⁻¹) = (k * k' * k⁻¹) (k w) * (k w)⁻¹ := by
      simp [MulAut.mul_apply, map_mul, map_inv]
    rw [e]
    exact Subgroup.subset_closure ⟨_, K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk), _,
      hW k hk w hw, rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

include hS in
theorem commV_le_commOn : commV (hS.kY lam hlam1) ≤
    G6.commOn (hS.kY lam hlam1) (commV (hS.kY lam hlam1)) := by
  set K := hS.kY lam hlam1
  have hW0s : Stab K (commV K) := (hS.stab_W0 lam hlam1).mono (hS.kY_le lam hlam1)
  have h1 : ∀ k ∈ K, ∀ y ∈ (⊤ : Subgroup (hS.YM lam)), k y * y⁻¹ ∈ commV K :=
    fun k hk y _ => Subgroup.subset_closure ⟨k, hk, y, rfl⟩
  have h2 : ∀ k ∈ K, ∀ w ∈ commV K, k w * w⁻¹ ∈ G6.commOn K (commV K) :=
    fun k hk w hw => mem_commOn_of hk hw
  have h3 := perfect_trivial_of_two_step (hS.kY_perfect lam hlam1) (stab_top K)
    (stab_commOn hW0s) h1 h2
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨k, hk, y, rfl⟩
  exact h3 k hk y (Subgroup.mem_top y)

theorem commV_kW_eq_top : commV (kW hS lam hlam1) = ⊤ := by
  set K := hS.kY lam hlam1
  rw [eq_top_iff]
  rintro w -
  induction w using QuotientGroup.induction_on with
  | H w =>
    have key : ∀ y (hy : y ∈ G6.commOn K (commV K)) (hyW : y ∈ commV K),
        (QuotientGroup.mk (⟨y, hyW⟩ : ↥(commV K)) : WM hS lam hlam1) ∈
          commV (kW hS lam hlam1) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        intro hyW
        obtain ⟨_, ⟨l, hl, rfl⟩, u, hu, rfl⟩ := hy
        refine Subgroup.subset_closure ⟨wRho hS lam hlam1 l, ⟨l, hl, rfl⟩,
          QuotientGroup.mk ⟨u, hu⟩, ?_⟩
        rw [secAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      | one =>
        intro h1
        exact Subgroup.one_mem _
      | mul a b ha hb iha ihb =>
        intro hab
        have haW : a ∈ commV K := (commOn_le ((hS.stab_W0 lam hlam1).mono
          (hS.kY_le lam hlam1))) ha
        have hbW : b ∈ commV K := (commOn_le ((hS.stab_W0 lam hlam1).mono
          (hS.kY_le lam hlam1))) hb
        have e : (⟨a * b, hab⟩ : ↥(commV K)) = ⟨a, haW⟩ * ⟨b, hbW⟩ := rfl
        rw [e, QuotientGroup.mk_mul]
        exact Subgroup.mul_mem _ (iha haW) (ihb hbW)
      | inv a ha iha =>
        intro hai
        have haW : a ∈ commV K := (commOn_le ((hS.stab_W0 lam hlam1).mono
          (hS.kY_le lam hlam1))) ha
        have e : (⟨a⁻¹, hai⟩ : ↥(commV K)) = (⟨a, haW⟩ : ↥(commV K))⁻¹ := rfl
        rw [e, QuotientGroup.mk_inv]
        exact Subgroup.inv_mem _ (iha haW)
    exact key w (commV_le_commOn hS lam hlam1 w.2) w.2

theorem zW_le_fixV_kW : zW hS lam hlam1 ≤ fixV (kW hS lam hlam1) := by
  rintro _ ⟨m, hm, rfl⟩ _ ⟨l, hl, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hm
  rw [QuotientGroup.mk'_apply, secAct_mk]
  congr 1
  exact Subtype.ext (hm.2 _ ⟨l, hl, rfl⟩)

theorem wRho_mem_zW (g : ↥G₀) {z : WM hS lam hlam1} (hz : z ∈ zW hS lam hlam1) :
    wRho hS lam hlam1 g z ∈ zW hS lam hlam1 := by
  obtain ⟨m, hm, rfl⟩ := hz
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hm
  refine ⟨⟨_, (hS.isInv_W0 lam hlam1) g _ m.2⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  exact (hS.isInv_M0 lam hlam1) g _ hm

end Cover

section Iso

variable (hinj : ∀ g : ↥G₀, (g : U₀) ∈ Lt → hS.secRho lam hlam1 g = 1 →
  wRho hS lam hlam1 g = 1)

noncomputable abbrev aW : ↥(Lt.subgroupOf G₀) →* MulAut (WM hS lam hlam1) :=
  (wRho hS lam hlam1).comp (Lt.subgroupOf G₀).subtype

noncomputable abbrev bS : ↥(Lt.subgroupOf G₀) →* MulAut (hS.SM lam hlam1) :=
  (hS.secRho lam hlam1).comp (Lt.subgroupOf G₀).subtype

theorem aW_range : (aW hS lam hlam1).range = kW hS lam hlam1 := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem bS_range : (bS hS lam hlam1).range = hS.kS lam hlam1 := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

include hinj in
theorem ker_aW_eq : (aW hS lam hlam1).ker = (bS hS lam hlam1).ker := by
  ext l
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact ⟨secRho_eq_one_of_wRho hS lam hlam1 _,
    hinj _ (Subgroup.mem_subgroupOf.mp l.2)⟩

noncomputable def eKW : ↥(kW hS lam hlam1) ≃* ↥(hS.kS lam hlam1) :=
  ((MulEquiv.subgroupCongr (aW_range hS lam hlam1)).symm.trans
    (QuotientGroup.quotientKerEquivRange (aW hS lam hlam1)).symm).trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_aW_eq hS lam hlam1 hinj)).trans
      ((QuotientGroup.quotientKerEquivRange (bS hS lam hlam1)).trans
        (MulEquiv.subgroupCongr (bS_range hS lam hlam1))))

theorem eKW_apply (l : ↥(Lt.subgroupOf G₀)) :
    ((eKW hS lam hlam1 hinj ⟨wRho hS lam hlam1 l, ⟨l, l.2, rfl⟩⟩ : ↥(hS.kS lam hlam1)) :
      MulAut (hS.SM lam hlam1)) = hS.secRho lam hlam1 l := by
  have h1 : (MulEquiv.subgroupCongr (aW_range hS lam hlam1)).symm
      ⟨wRho hS lam hlam1 l, ⟨l, l.2, rfl⟩⟩ = (aW hS lam hlam1).rangeRestrict l := rfl
  simp only [eKW, MulEquiv.trans_apply, h1]
  rw [show (QuotientGroup.quotientKerEquivRange (aW hS lam hlam1)).symm
      ((aW hS lam hlam1).rangeRestrict l) = QuotientGroup.mk l from
    (MulEquiv.symm_apply_eq _).mpr rfl]
  rfl

theorem qWS_eKW (k : ↥(kW hS lam hlam1)) (w : WM hS lam hlam1) :
    qWS hS lam hlam1 ((k : MulAut (WM hS lam hlam1)) w) =
      ((eKW hS lam hlam1 hinj k : ↥(hS.kS lam hlam1)) : MulAut (hS.SM lam hlam1))
        (qWS hS lam hlam1 w) := by
  obtain ⟨_, ⟨l, hl, rfl⟩⟩ := k
  have := eKW_apply hS lam hlam1 hinj ⟨l, hl⟩
  rw [this]
  exact qWS_wRho hS lam hlam1 l w

include hinj in
theorem altNat_kW (hK : AlternatingNatural (hS.kS lam hlam1) ⊤ ⊥ 6) :
    AlternatingNatural (kW hS lam hlam1) ⊤ (zW hS lam hlam1) 6 := by
  obtain ⟨π, hπs, -, hkerle, -, -, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hK
  set eK := eKW hS lam hlam1 hinj
  let qT : ↥(⊤ : Subgroup (WM hS lam hlam1)) →* ↥(⊤ : Subgroup (hS.SM lam hlam1)) :=
    ((qWS hS lam hlam1).comp (⊤ : Subgroup (WM hS lam hlam1)).subtype).codRestrict ⊤
      fun _ => Subgroup.mem_top _
  have hqT : ∀ u, ((qT u : ↥(⊤ : Subgroup (hS.SM lam hlam1))) : hS.SM lam hlam1) =
      qWS hS lam hlam1 u := fun _ => rfl
  refine ⟨eK.symm.toMonoidHom.comp π, ?_, le_top, hkerle, fun _ _ _ => Subgroup.mem_top _,
    ?_, hsec, hkerinv, β.comp qT, ?_, ?_, ?_⟩
  · exact eK.symm.surjective.comp hπs
  · rintro ⟨_, ⟨l, hl, rfl⟩⟩ z hz
    exact wRho_mem_zW hS lam hlam1 l hz
  · intro t
    obtain ⟨s, rfl⟩ := hβs t
    obtain ⟨w, hw⟩ := qWS_surjective hS lam hlam1 s
    refine ⟨⟨w, Subgroup.mem_top w⟩, ?_⟩
    show β (qT _) = _
    congr 1
    exact Subtype.ext hw
  · intro u
    rw [MonoidHom.comp_apply, hβk, Subgroup.mem_bot, hqT, qWS_eq_one_iff]
  · intro γ u m hu hm h1
    have h2 : qT ⟨((eK.symm.toMonoidHom.comp π γ : ↥(kW hS lam hlam1)) :
        MulAut (WM hS lam hlam1)) u, hu⟩ =
        ⟨((π γ : ↥(hS.kS lam hlam1)) : MulAut (hS.SM lam hlam1)) (qT u : hS.SM lam hlam1),
          Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      rw [hqT, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, qWS_eKW hS lam hlam1 hinj,
        MulEquiv.apply_symm_apply]
      rfl
    rw [MonoidHom.comp_apply, h2]
    exact hβe γ (qT u) m (Subgroup.mem_top _) hm h1

end Iso

section M0

include hS in
theorem card_commV_eY_le : Nat.card (commV (hS.eY lam hlam1)) ≤ e := by
  have : Finite (hS.YM lam) := hS.finite_YM lam
  have h1 := (yPairing hS.cls2 lam).card_commV_mul_card_fixV
    ((hS.pairing_isInv lam hlam1).mono (hS.eY_le lam hlam1))
  have h2 := (fixV (hS.eY lam hlam1)).index_mul_card
  have hpos : 0 < Nat.card (fixV (hS.eY lam hlam1)) := Nat.card_pos
  have h3 : Nat.card (commV (hS.eY lam hlam1)) = (fixV (hS.eY lam hlam1)).index := by
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  rw [h3]
  exact hS.index_fixV_eY_le lam hlam1

theorem card_commV_eW_le :
    Nat.card (commV (eW hS lam hlam1)) ≤ Nat.card (commV (hS.eY lam hlam1)) := by
  have : Finite (hS.YM lam) := hS.finite_YM lam
  have hle : (commV (eW hS lam hlam1)).map (iWY hS lam hlam1) ≤ commV (hS.eY lam hlam1) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨_, ⟨g, hg, rfl⟩, w, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv, iWY_wRho]
    exact Subgroup.subset_closure ⟨_, ⟨g, hg, rfl⟩, _, rfl⟩
  rw [← Subgroup.card_map_of_injective (iWY_injective hS lam hlam1)]
  exact Subgroup.card_le_of_le hle

theorem exists_two_ne_one {H : Type*} [Group H] {S : Subgroup H} [Finite S]
    (h3 : 3 ≤ Nat.card S) : ∃ s₁ ∈ S, s₁ ≠ 1 ∧ ∃ s₂ ∈ S, s₂ ≠ 1 ∧ s₂ ≠ s₁ := by
  classical
  by_contra hcon
  push Not at hcon
  have hS1 : ∃ s₁ ∈ S, s₁ ≠ 1 := by
    by_contra h0
    push Not at h0
    have : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr h0
    rw [this, Subgroup.card_bot] at h3
    omega
  obtain ⟨s₁, hs₁, hs₁1⟩ := hS1
  have hsub : (S : Set H) ⊆ {1, s₁} := by
    intro s hs
    by_cases h1 : s = 1
    · exact Or.inl h1
    · exact Or.inr (hcon s₁ hs₁ hs₁1 s hs h1)
  have h4 : Nat.card ↥(S : Set H) ≤ Nat.card ↥({1, s₁} : Set H) :=
    Nat.card_mono (Set.toFinite _) hsub
  have h5 : Nat.card ↥({1, s₁} : Set H) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have h6 : Nat.card ↥(S : Set H) = Nat.card S := rfl
  omega

variable (hinj : ∀ g : ↥G₀, (g : U₀) ∈ Lt → hS.secRho lam hlam1 g = 1 →
  wRho hS lam hlam1 g = 1)

include hinj in
theorem m0_eq_bot
    (hirr : IrrSec (hS.rho lam hlam1).range (commV (hS.kY lam hlam1))
      (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)))
    (he4 : e = 4) (hA0 : eW hS lam hlam1 ≤ kW hS lam hlam1)
    (hK : AlternatingNatural (hS.kS lam hlam1) ⊤ ⊥ 6) :
    commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1) = ⊥ := by
  rcases H13.VolI.altNaturalCoverSix_holds (WM hS lam hlam1) (sq_WM hS lam hlam1)
      (kW hS lam hlam1) (zW hS lam hlam1) (zW_le_fixV_kW hS lam hlam1)
      (commV_kW_eq_top hS lam hlam1) (altNat_kW hS lam hlam1 hinj hK) with h0 | ⟨-, -, hR⟩
  ·
    rw [eq_bot_iff]
    intro m hm
    have hmW : m ∈ commV (hS.kY lam hlam1) := hm.1
    have hz : (QuotientGroup.mk (⟨m, hmW⟩ : ↥(commV (hS.kY lam hlam1))) :
        WM hS lam hlam1) ∈ zW hS lam hlam1 :=
      ⟨⟨m, hmW⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
    rw [h0, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hz
    exact hz
  ·
    exfalso
    obtain ⟨π', hR'⟩ := hR
    have : Finite ↥(hS.eS lam hlam1) := inferInstance
    have h3 : 3 ≤ Nat.card ↥(hS.eS lam hlam1) := by
      have := hS.le_card_eS lam hlam1 hirr
      omega
    obtain ⟨s₁, hs₁, hs₁1, s₂, hs₂, hs₂1, hs₂₁⟩ := exists_two_ne_one h3
    obtain ⟨g₁, hg₁, rfl⟩ := hs₁
    obtain ⟨g₂, hg₂, rfl⟩ := hs₂
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg₁ hg₂
    have hsq : ∀ g : ↥G₀, (g : U₀) ∈ E → wRho hS lam hlam1 g * wRho hS lam hlam1 g = 1 := by
      intro g hg
      have h2 : g * g = 1 := Subtype.ext (by
        have := hS.e_ab.2 _ hg
        simpa [pow_two] using this)
      rw [← map_mul, h2, map_one]
    have hx₁E : wRho hS lam hlam1 g₁ ∈ eW hS lam hlam1 := ⟨g₁, hg₁, rfl⟩
    have hx₂E : wRho hS lam hlam1 g₂ ∈ eW hS lam hlam1 := ⟨g₂, hg₂, rfl⟩
    have hne1 : ∀ g : ↥G₀, hS.secRho lam hlam1 g ≠ 1 → wRho hS lam hlam1 g ≠ 1 :=
      fun g hg h1 => hg (secRho_eq_one_of_wRho hS lam hlam1 g h1)
    have hne : wRho hS lam hlam1 g₁ ≠ wRho hS lam hlam1 g₂ := by
      intro h12
      apply hs₂₁
      have h1 : wRho hS lam hlam1 (g₁⁻¹ * g₂) = 1 := by rw [map_mul, map_inv, h12, inv_mul_cancel]
      have h2 := secRho_eq_one_of_wRho hS lam hlam1 _ h1
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2.symm
    have h8 := card_commV_ge_eight (sq_WM hS lam hlam1) hR' hx₁E hx₂E (hA0 hx₁E) (hA0 hx₂E) hne
      (hne1 g₁ hs₁1) (hne1 g₂ hs₂1) (hsq g₁ hg₁) (hsq g₂ hg₂)
    have h4 := (card_commV_eW_le hS lam hlam1).trans (card_commV_eY_le hS lam hlam1)
    omega

end M0

end CFSG.Quasithin.MS93.S38EA
