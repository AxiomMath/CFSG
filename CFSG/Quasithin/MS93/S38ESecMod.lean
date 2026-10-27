module

public import CFSG.Quasithin.MS93.S38EIrr
public import CFSG.Quasithin.MS93.S38ESec

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.B3
open scoped commutatorElement

namespace Pairing

variable {Y Q : Type*} [CommGroup Y] [CommGroup Q] (p : Pairing Y Q) {W N : Subgroup Y}
  (hN : N ≤ p.perp W) (hrad : W ⊓ p.perp W ≤ N)

@[expose] noncomputable def secLeft (b : ↥W) : Sec W N →* Q :=
  QuotientGroup.lift (N.subgroupOf W)
    { toFun := fun a => p.f a b
      map_one' := p.one_left _
      map_mul' := fun _ _ => p.map_mul_left _ _ _ }
    (fun _ ha => hN (Subgroup.mem_subgroupOf.mp ha) b b.2)

@[expose] noncomputable def secHom : Sec W N →* (Sec W N →* Q) :=
  QuotientGroup.lift (N.subgroupOf W)
    { toFun := fun b => p.secLeft hN b
      map_one' := MonoidHom.ext fun a => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          show p.f (a : Y) ((1 : ↥W) : Y) = 1
          exact p.one_right _
      map_mul' := fun b b' => MonoidHom.ext fun a => by
        induction a using QuotientGroup.induction_on with
        | H a =>
          show p.f (a : Y) ((b * b' : ↥W) : Y) = p.f (a : Y) b * p.f (a : Y) b'
          exact p.map_mul_right _ _ _ }
    (fun b hb => MonoidHom.ext fun a => by
      induction a using QuotientGroup.induction_on with
      | H a =>
        show p.f (a : Y) (b : Y) = 1
        rw [p.swap, hN (Subgroup.mem_subgroupOf.mp hb) a a.2, inv_one])

@[expose] noncomputable def secPairing : Pairing (Sec W N) Q where
  f a b := p.secHom hN b a
  map_mul_left a b c := map_mul _ a b
  map_mul_right a b c := by rw [map_mul, MonoidHom.mul_apply]
  self a := by
    induction a using QuotientGroup.induction_on with
    | H a => exact p.self _
  nondeg a ha := by
    induction a using QuotientGroup.induction_on with
    | H a =>
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      refine hrad ⟨a.2, fun s hs => ?_⟩
      exact ha (QuotientGroup.mk ⟨s, hs⟩)

theorem secPairing_f_mk (a b : ↥W) :
    (p.secPairing hN hrad).f (QuotientGroup.mk a) (QuotientGroup.mk b) = p.f a b := rfl

theorem secPairing_isInv {G : Type*} [Group G] (ρ : G →* MulAut Y) (hp : p.IsInv ρ.range)
    (hW : B3.IsInv ρ W) (hNi : B3.IsInv ρ N) :
    (p.secPairing hN hrad).IsInv (secAct ρ hW hNi).range := by
  rintro _ ⟨g, rfl⟩ a b
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [secAct_mk, secAct_mk, secPairing_f_mk, secPairing_f_mk]
      exact hp _ ⟨g, rfl⟩ _ _

end Pairing

section Card

variable {G H : Type*} [Group G] [Group H]

theorem card_map_eq_relIndex_ker (f : G →* H) (A : Subgroup G) :
    Nat.card (A.map f) = f.ker.relIndex A := by
  rw [← MonoidHom.domRestrict_range, ← Subgroup.index_ker, MonoidHom.ker_domRestrict]
  rfl

theorem fixV_ne_bot_of_isPGroup {F : Type*} [CommGroup F] [Finite F] [Nontrivial F]
    (hsq : ∀ v : F, v ^ 2 = 1) {P : Subgroup (MulAut F)} (hP : IsPGroup 2 ↥P) :
    fixV P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints F
  have hfix : Nat.card (MulAction.fixedPoints ↥P F) = Nat.card (fixV P) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [hfix] at hmod
  have hV2 : IsPGroup 2 F := fun v => ⟨1, by rw [pow_one]; exact hsq v⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  have heven : Nat.card F % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hmod
  have := hmod.symm
  unfold Nat.ModEq at this
  omega

end Card

namespace EndSetup

variable {U₀ : Type*} [Group U₀] {V G₀ Lt Tb Qa E : Subgroup U₀} {e : ℕ}
  (hS : EndSetup V G₀ Lt Tb Qa E e) (lam : ↥⁅V, V⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, V⁆, Tb⁆ → lam c = 1)

theorem stab_W0 :
    Stab (hS.rho lam hlam1).range (commV (hS.kY lam hlam1)) :=
  stab_commV (hS.range_le_normalizer_kY lam hlam1)

theorem stab_M0 :
    Stab (hS.rho lam hlam1).range (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)) :=
  stab_inf (hS.stab_W0 lam hlam1) (stab_fixV (hS.range_le_normalizer_kY lam hlam1))

theorem isInv_W0 : B3.IsInv (hS.rho lam hlam1) (commV (hS.kY lam hlam1)) :=
  fun g w hw => hS.stab_W0 lam hlam1 _ ⟨g, rfl⟩ w hw

theorem isInv_M0 :
    B3.IsInv (hS.rho lam hlam1) (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)) :=
  fun g w hw => hS.stab_M0 lam hlam1 _ ⟨g, rfl⟩ w hw

abbrev SM : Type _ :=
  Sec (commV (hS.kY lam hlam1)) (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1))

noncomputable abbrev secRho : ↥G₀ →* MulAut (hS.SM lam hlam1) :=
  secAct (hS.rho lam hlam1) (hS.isInv_W0 lam hlam1) (hS.isInv_M0 lam hlam1)

theorem pairing_isInv_kY : (yPairing hS.cls2 lam).IsInv (hS.kY lam hlam1) :=
  (hS.pairing_isInv lam hlam1).mono (hS.kY_le lam hlam1)

theorem M0_le_perp : commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1) ≤
    (yPairing hS.cls2 lam).perp (commV (hS.kY lam hlam1)) := by
  rw [Pairing.perp_commV_eq_fixV _ (hS.pairing_isInv_kY lam hlam1)]
  exact inf_le_right

theorem rad_le_M0 : commV (hS.kY lam hlam1) ⊓
    (yPairing hS.cls2 lam).perp (commV (hS.kY lam hlam1)) ≤
      commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1) := by
  rw [Pairing.perp_commV_eq_fixV _ (hS.pairing_isInv_kY lam hlam1)]

noncomputable abbrev secPair : Pairing (hS.SM lam hlam1) ℂˣ :=
  (yPairing hS.cls2 lam).secPairing (hS.M0_le_perp lam hlam1) (hS.rad_le_M0 lam hlam1)

theorem secPair_isInv : (hS.secPair lam hlam1).IsInv (hS.secRho lam hlam1).range :=
  Pairing.secPairing_isInv _ _ _ _ (hS.pairing_isInv lam hlam1) _ _

include hS in
theorem finite_SM : Finite (hS.SM lam hlam1) :=
  have : Finite (hS.YM lam) := hS.finite_YM lam
  inferInstance

instance instFiniteSM : Finite (hS.SM lam hlam1) := hS.finite_SM lam hlam1

include hS in
theorem sq_SM (s : hS.SM lam hlam1) : s ^ 2 = 1 := sec_sq (hS.sq_eq_one lam) s

theorem card_commV_mul_card_fixV_SM {P : Subgroup (MulAut (hS.SM lam hlam1))}
    (hP : P ≤ (hS.secRho lam hlam1).range) :
    Nat.card (commV P) * Nat.card (fixV P) = Nat.card (hS.SM lam hlam1) := by
  have : Finite (hS.SM lam hlam1) := hS.finite_SM lam hlam1
  exact (hS.secPair lam hlam1).card_commV_mul_card_fixV ((hS.secPair_isInv lam hlam1).mono hP)

theorem secRho_eq_one_iff (g : ↥G₀) : hS.secRho lam hlam1 g = 1 ↔
    ∀ w ∈ commV (hS.kY lam hlam1), hS.rho lam hlam1 g w * w⁻¹ ∈
      commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1) :=
  secAct_eq_one_iff _ _ _

noncomputable abbrev eS : Subgroup (MulAut (hS.SM lam hlam1)) :=
  (E.subgroupOf G₀).map (hS.secRho lam hlam1)

noncomputable abbrev kS : Subgroup (MulAut (hS.SM lam hlam1)) :=
  (Lt.subgroupOf G₀).map (hS.secRho lam hlam1)

theorem index_fixV_eS_le : (fixV (hS.eS lam hlam1)).index ≤ e := by
  have : Finite (hS.YM lam) := hS.finite_YM lam
  rw [index_fixV_sec (hS.isInv_W0 lam hlam1) (hS.isInv_M0 lam hlam1) inf_le_left]
  have hW := (hS.stab_W0 lam hlam1).mono (hS.eY_le lam hlam1)
  have hM := (hS.stab_M0 lam hlam1).mono (hS.eY_le lam hlam1)
  calc aI (hS.eY lam hlam1) (commV (hS.kY lam hlam1))
        (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1))
      ≤ aI (hS.eY lam hlam1) ⊤ (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)) :=
        aI_le_of_le hW inf_le_left le_top
    _ ≤ aI (hS.eY lam hlam1) ⊤ ⊥ := aI_le_of_le' hM bot_le le_top
    _ = (fixV (hS.eY lam hlam1)).index := aI_top_bot _
    _ ≤ e := hS.index_fixV_eY_le lam hlam1

theorem isElemAbelian2_eS : IsElemAbelian2 (hS.eS lam hlam1) := by
  obtain ⟨hcomm, hsq⟩ := hS.e_ab
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact setLike_mul_comm (s := E) ha hb
  · rintro _ ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hsq _ ha)
    rw [this, map_one]

variable (hirr : IrrSec (hS.rho lam hlam1).range (commV (hS.kY lam hlam1))
    (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)))
include hirr

theorem nonCent_sec :
    NonCent (hS.kY lam hlam1) (commV (hS.kY lam hlam1))
      (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)) := by
  by_contra hnc
  unfold NonCent at hnc
  push Not at hnc
  have hK := (hS.stab_W0 lam hlam1).mono (hS.kY_le lam hlam1)
  have h1 := perfect_trivial_of_two_step (hS.kY_perfect lam hlam1) hK (stab_bot _)
    (fun k hk w hw => (hnc k hk w hw).2)
    (fun k hk w hw => by
      rw [Subgroup.mem_bot, mul_inv_eq_one]
      exact hw k hk)
  have h2 : commV (hS.kY lam hlam1) ≤ commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1) :=
    fun w hw => ⟨hw, fun k hk => by
      have := h1 k hk w hw
      rwa [Subgroup.mem_bot, mul_inv_eq_one] at this⟩
  exact (lt_irrefl _) (lt_of_lt_of_le hirr.1 h2)

theorem exists_lt_secRho_ne_one :
    ∃ g : ↥G₀, (g : U₀) ∈ Lt ∧ hS.secRho lam hlam1 g ≠ 1 := by
  obtain ⟨k, hk, w, hw, hkw⟩ := hS.nonCent_sec lam hlam1 hirr
  obtain ⟨g, hg, hgk⟩ := hk
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg
  refine ⟨g, hg, fun h1 => hkw ?_⟩
  rw [← hgk]
  exact (hS.secRho_eq_one_iff lam hlam1 g).mp h1 w hw

theorem nontrivial_SM : Nontrivial (hS.SM lam hlam1) := by
  obtain ⟨k, hk, w, hw, hkw⟩ := hS.nonCent_sec lam hlam1 hirr
  refine ⟨⟨QuotientGroup.mk ⟨w, hw⟩, 1, fun h => hkw ?_⟩⟩
  have h1 : (⟨w, hw⟩ : ↥(commV (hS.kY lam hlam1))) ∈
      (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)).subgroupOf (commV (hS.kY lam hlam1)) :=
    (QuotientGroup.eq_one_iff _).mp h
  rw [Subgroup.mem_subgroupOf] at h1
  rw [h1.2 k hk, mul_inv_cancel]
  exact one_mem _

theorem irr_SM (J : Subgroup (hS.SM lam hlam1))
    (hJ : ∀ g : ↥G₀, ∀ s ∈ J, hS.secRho lam hlam1 g s ∈ J) : J = ⊥ ∨ J = ⊤ := by
  refine sec_irr _ _ inf_le_left (fun J' hJ' h1 h2 => ?_) J hJ
  exact hirr.2.2.2 J' (fun x hx w hw => by obtain ⟨g, rfl⟩ := hx; exact hJ' g w hw) h1 h2

theorem secRho_eq_one_of_mem {P : Subgroup U₀} (hPG : P ≤ G₀)
    (hPn : G₀ ≤ Subgroup.normalizer (P : Set U₀)) (hP2 : IsPGroup 2 ↥P) {g : U₀} (hg : g ∈ P) :
    hS.secRho lam hlam1 ⟨g, hPG hg⟩ = 1 := by
  have : Finite (hS.SM lam hlam1) := hS.finite_SM lam hlam1
  have : Nontrivial (hS.SM lam hlam1) := hS.nontrivial_SM lam hlam1 hirr
  set P' := (P.subgroupOf G₀).map (hS.secRho lam hlam1)
  have hP'2 : IsPGroup 2 ↥P' := by
    have h1 : IsPGroup 2 ↥(P.subgroupOf G₀) :=
      hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPG).symm
    exact h1.map _
  have hfix := fixV_ne_bot_of_isPGroup (hS.sq_SM lam hlam1) hP'2
  have hinv : ∀ h : ↥G₀, ∀ s ∈ fixV P', hS.secRho lam hlam1 h s ∈ fixV P' := by
    intro h s hs x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : h⁻¹ * y * h ∈ P.subgroupOf G₀ := by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp (hPn (G₀.inv_mem h.2)) y).mp hy
      simpa using this
    have h1 := hs _ ⟨h⁻¹ * y * h, hy', rfl⟩
    have e : hS.secRho lam hlam1 y (hS.secRho lam hlam1 h s) =
        hS.secRho lam hlam1 h (hS.secRho lam hlam1 (h⁻¹ * y * h) s) := by
      rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    rw [e, h1]
  rcases hS.irr_SM lam hlam1 hirr _ hinv with hb | ht
  · exact absurd hb hfix
  · ext s
    have hs : s ∈ fixV P' := by rw [ht]; exact Subgroup.mem_top s
    have := hs _ ⟨⟨g, hPG hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    simpa using this

theorem le_card_eS : e ≤ Nat.card (hS.eS lam hlam1) := by
  rw [card_map_eq_relIndex_ker]
  have h1 := hS.le_relIndex_kerRel lam hlam1 _ _ hirr (hS.nonCent_sec lam hlam1 hirr)
  refine h1.trans (le_of_eq ?_)
  rw [← Subgroup.relIndex_comap, ← Subgroup.inf_relIndex_right,
    ← Subgroup.inf_relIndex_right (hS.secRho lam hlam1).ker]
  congr 1
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker, mem_kerRel,
    hS.secRho_eq_one_iff lam hlam1]
  constructor
  · rintro ⟨⟨-, h⟩, hg⟩
    exact ⟨h, hg⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨Subgroup.mem_map_of_mem _ hg, h⟩, hg⟩

theorem card_le_card_eS_mul :
    Nat.card (hS.SM lam hlam1) ≤
      Nat.card (hS.eS lam hlam1) * Nat.card (fixV (hS.eS lam hlam1)) := by
  rw [← (fixV (hS.eS lam hlam1)).index_mul_card]
  exact Nat.mul_le_mul_right _
    ((hS.index_fixV_eS_le lam hlam1).trans (hS.le_card_eS lam hlam1 hirr))

theorem eS_ne_bot (he2 : 2 ≤ e) : hS.eS lam hlam1 ≠ ⊥ := by
  intro hbot
  have h := hS.le_card_eS lam hlam1 hirr
  rw [hbot, Subgroup.card_bot] at h
  omega

section Comp

variable {H : Type*} [Group H] (φ : H →* ↥G₀) (hφ : Function.Surjective φ)
include hφ

omit hirr in
theorem range_secRho_comp : ((hS.secRho lam hlam1).comp φ).range = (hS.secRho lam hlam1).range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ, ← MonoidHom.range_eq_map]

omit hφ in
theorem secRho_comp_eq_one {P : Subgroup U₀} (hPG : P ≤ G₀)
    (hPn : G₀ ≤ Subgroup.normalizer (P : Set U₀)) (hP2 : IsPGroup 2 ↥P) {x : H}
    (hx : (φ x : U₀) ∈ P) : (hS.secRho lam hlam1).comp φ x = 1 := by
  have e : φ x = ⟨(φ x : U₀), hPG hx⟩ := rfl
  rw [MonoidHom.comp_apply, e]
  exact hS.secRho_eq_one_of_mem lam hlam1 hirr hPG hPn hP2 hx

theorem irr_secRho_comp (J : Subgroup (hS.SM lam hlam1))
    (hJ : ∀ x : H, ∀ s ∈ J, (hS.secRho lam hlam1).comp φ x s ∈ J) : J = ⊥ ∨ J = ⊤ := by
  refine hS.irr_SM lam hlam1 hirr J fun g s hs => ?_
  obtain ⟨x, rfl⟩ := hφ g
  exact hJ x s hs

theorem exists_secRho_comp_ne_one :
    ∃ x : H, (φ x : U₀) ∈ Lt ∧ (hS.secRho lam hlam1).comp φ x ≠ 1 := by
  obtain ⟨g, hgL, hg1⟩ := hS.exists_lt_secRho_ne_one lam hlam1 hirr
  obtain ⟨x, rfl⟩ := hφ g
  exact ⟨x, hgL, hg1⟩

end Comp

end EndSetup

end CFSG.Quasithin.MS93.S38E
