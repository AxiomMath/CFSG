module

public import CFSG.Quasithin.MS93.S38ESecMod

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.B3
open scoped commutatorElement

section CommV

variable {G : Type*} [Group G] {Y : Type*} [CommGroup Y] {ρ : G →* MulAut Y}
  {W N : Subgroup Y} (hW : B3.IsInv ρ W) (hN : B3.IsInv ρ N)

include hW hN in
theorem card_commV_sec [Finite Y] (hNW : N ≤ W) (B : Subgroup G) :
    Nat.card (commV (B.map (secAct ρ hW hN))) = cI (B.map ρ) W N := by
  set D := G6.commOn (B.map ρ) W ⊔ N with hD
  have hWE : Stab (B.map ρ) W := by
    rintro _ ⟨b, -, rfl⟩ w hw
    exact hW b w hw
  have hDW : D ≤ W := sup_le (commOn_le hWE) hNW
  have hQ : commV (B.map (secAct ρ hW hN)) =
      (D.subgroupOf W).map (QuotientGroup.mk' (N.subgroupOf W)) := by
    apply le_antisymm
    · rw [commV, Subgroup.closure_le]
      rintro _ ⟨_, ⟨b, hb, rfl⟩, s, rfl⟩
      induction s using QuotientGroup.induction_on with
      | H w =>
        refine ⟨⟨ρ b w, hW b w w.2⟩ * w⁻¹, ?_, ?_⟩
        · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
          exact le_sup_left (b := N) (mem_commOn_of (Subgroup.mem_map_of_mem _ hb) w.2)
        · rw [map_mul, map_inv]
          rfl
    · rintro _ ⟨d, hd, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hd
      have hDR : D ≤ ((commV (B.map (secAct ρ hW hN))).comap
          (QuotientGroup.mk' (N.subgroupOf W))).map W.subtype := by
        refine sup_le ?_ fun n hn => ⟨⟨n, hNW hn⟩, ?_, rfl⟩
        · rw [G6.commOn, Subgroup.closure_le]
          rintro _ ⟨e, he, w, hw, rfl⟩
          obtain ⟨b, hb, rfl⟩ := he
          refine ⟨⟨ρ b w, hW b w hw⟩ * ⟨w, hw⟩⁻¹, ?_, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
          exact Subgroup.subset_closure ⟨_, Subgroup.mem_map_of_mem _ hb,
            QuotientGroup.mk ⟨w, hw⟩, rfl⟩
        · have h1 : QuotientGroup.mk' (N.subgroupOf W) (⟨n, hNW hn⟩ : ↥W) = 1 :=
            (QuotientGroup.eq_one_iff (⟨n, hNW hn⟩ : ↥W)).mpr (Subgroup.mem_subgroupOf.mpr hn)
          rw [SetLike.mem_coe, Subgroup.mem_comap, h1]
          exact one_mem _
      obtain ⟨r, hr, hrd⟩ := hDR hd
      have : r = d := Subtype.ext hrd
      rw [← this]
      exact hr
  rw [hQ]
  have h1 := card_map_mk_mul_card (D.subgroupOf W) (N.subgroupOf W)
    (fun x hx => Subgroup.mem_subgroupOf.mpr (le_sup_right (a := G6.commOn (B.map ρ) W)
      (Subgroup.mem_subgroupOf.mp hx)))
  have h2 : Nat.card ↥(D.subgroupOf W) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDW).toEquiv
  have h3 : Nat.card ↥(N.subgroupOf W) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv
  have h4 := N.relIndex_mul_card (K := D)
  rw [inf_eq_left.mpr le_sup_right] at h4
  rw [h2, h3, ← h4] at h1
  have hpos : 0 < Nat.card N := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

end CommV

namespace EndSetup

variable {U₀ : Type*} [Group U₀] {V G₀ Lt Tb Qa E : Subgroup U₀} {e : ℕ}
  (hS : EndSetup V G₀ Lt Tb Qa E e) (lam : ↥⁅V, V⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, V⁆, Tb⁆ → lam c = 1)

theorem isInv_of_stab {A : Subgroup (hS.YM lam)} (hA : Stab (hS.rho lam hlam1).range A) :
    B3.IsInv (hS.rho lam hlam1) A := fun g w hw => hA _ ⟨g, rfl⟩ w hw

include hS in
theorem finite_gSM (W N : Subgroup (hS.YM lam)) : Finite (Sec W N) :=
  have : Finite (hS.YM lam) := hS.finite_YM lam
  inferInstance

include hS in
theorem sq_gSM (W N : Subgroup (hS.YM lam)) (s : Sec W N) : s ^ 2 = 1 :=
  sec_sq (hS.sq_eq_one lam) s

variable (W N : Subgroup (hS.YM lam)) (hirr : IrrSec (hS.rho lam hlam1).range W N)
include hirr

noncomputable abbrev gSecRho : ↥G₀ →* MulAut (Sec W N) :=
  secAct (hS.rho lam hlam1) (hS.isInv_of_stab lam hlam1 hirr.2.1)
    (hS.isInv_of_stab lam hlam1 hirr.2.2.1)

noncomputable abbrev geS : Subgroup (MulAut (Sec W N)) :=
  (E.subgroupOf G₀).map (hS.gSecRho lam hlam1 W N hirr)

theorem gSecRho_eq_one_iff (g : ↥G₀) : hS.gSecRho lam hlam1 W N hirr g = 1 ↔
    ∀ w ∈ W, hS.rho lam hlam1 g w * w⁻¹ ∈ N :=
  secAct_eq_one_iff _ _ _

theorem index_fixV_geS : (fixV (hS.geS lam hlam1 W N hirr)).index = aI (hS.eY lam hlam1) W N := by
  have : Finite (hS.YM lam) := hS.finite_YM lam
  exact index_fixV_sec (hS.isInv_of_stab lam hlam1 hirr.2.1)
    (hS.isInv_of_stab lam hlam1 hirr.2.2.1) hirr.1.le (E.subgroupOf G₀)

theorem index_fixV_geS_le : (fixV (hS.geS lam hlam1 W N hirr)).index ≤ e := by
  have : Finite (hS.YM lam) := hS.finite_YM lam
  rw [hS.index_fixV_geS lam hlam1 W N hirr]
  have hW := hirr.2.1.mono (hS.eY_le lam hlam1)
  have hN := hirr.2.2.1.mono (hS.eY_le lam hlam1)
  calc aI (hS.eY lam hlam1) W N ≤ aI (hS.eY lam hlam1) ⊤ N := aI_le_of_le hW hirr.1.le le_top
    _ ≤ aI (hS.eY lam hlam1) ⊤ ⊥ := aI_le_of_le' hN bot_le le_top
    _ = (fixV (hS.eY lam hlam1)).index := aI_top_bot _
    _ ≤ e := hS.index_fixV_eY_le lam hlam1

theorem card_commV_geS :
    Nat.card (commV (hS.geS lam hlam1 W N hirr)) = cI (hS.eY lam hlam1) W N := by
  have : Finite (hS.YM lam) := hS.finite_YM lam
  exact card_commV_sec (hS.isInv_of_stab lam hlam1 hirr.2.1)
    (hS.isInv_of_stab lam hlam1 hirr.2.2.1) hirr.1.le (E.subgroupOf G₀)

theorem isElemAbelian2_geS : IsElemAbelian2 (hS.geS lam hlam1 W N hirr) := by
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

variable (hnc : NonCent (hS.kY lam hlam1) W N)
include hnc

theorem exists_lt_gSecRho_ne_one :
    ∃ g : ↥G₀, (g : U₀) ∈ Lt ∧ hS.gSecRho lam hlam1 W N hirr g ≠ 1 := by
  obtain ⟨k, hk, w, hw, hkw⟩ := hnc
  obtain ⟨g, hg, hgk⟩ := hk
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg
  refine ⟨g, hg, fun h1 => hkw ?_⟩
  rw [← hgk]
  exact (hS.gSecRho_eq_one_iff lam hlam1 W N hirr g).mp h1 w hw

theorem nontrivial_gSM : Nontrivial (Sec W N) := by
  obtain ⟨k, hk, w, hw, hkw⟩ := hnc
  refine ⟨⟨QuotientGroup.mk ⟨w, hw⟩, 1, fun h => hkw ?_⟩⟩
  have h1 : (⟨w, hw⟩ : ↥W) ∈ N.subgroupOf W := (QuotientGroup.eq_one_iff _).mp h
  rw [Subgroup.mem_subgroupOf] at h1
  exact N.mul_mem (hirr.2.2.1 _ ((hS.kY_le lam hlam1) hk) _ h1) (N.inv_mem h1)

omit hnc in
theorem irr_gSM (J : Subgroup (Sec W N))
    (hJ : ∀ g : ↥G₀, ∀ s ∈ J, hS.gSecRho lam hlam1 W N hirr g s ∈ J) : J = ⊥ ∨ J = ⊤ := by
  refine sec_irr _ _ hirr.1.le (fun J' hJ' h1 h2 => ?_) J hJ
  exact hirr.2.2.2 J' (fun x hx w hw => by obtain ⟨g, rfl⟩ := hx; exact hJ' g w hw) h1 h2

theorem gSecRho_eq_one_of_mem {P : Subgroup U₀} (hPG : P ≤ G₀)
    (hPn : G₀ ≤ Subgroup.normalizer (P : Set U₀)) (hP2 : IsPGroup 2 ↥P) {g : U₀} (hg : g ∈ P) :
    hS.gSecRho lam hlam1 W N hirr ⟨g, hPG hg⟩ = 1 := by
  have : Nontrivial (Sec W N) := hS.nontrivial_gSM lam hlam1 W N hirr hnc
  set P' := (P.subgroupOf G₀).map (hS.gSecRho lam hlam1 W N hirr)
  have hP'2 : IsPGroup 2 ↥P' := by
    have h1 : IsPGroup 2 ↥(P.subgroupOf G₀) :=
      hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPG).symm
    exact h1.map _
  have : Finite (Sec W N) := hS.finite_gSM lam W N
  have hfix := fixV_ne_bot_of_isPGroup (hS.sq_gSM lam W N) hP'2
  have hinv : ∀ h : ↥G₀, ∀ s ∈ fixV P', hS.gSecRho lam hlam1 W N hirr h s ∈ fixV P' := by
    intro h s hs x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : h⁻¹ * y * h ∈ P.subgroupOf G₀ := by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp (hPn (G₀.inv_mem h.2)) y).mp hy
      simpa using this
    have h1 := hs _ ⟨h⁻¹ * y * h, hy', rfl⟩
    have e : hS.gSecRho lam hlam1 W N hirr y (hS.gSecRho lam hlam1 W N hirr h s) =
        hS.gSecRho lam hlam1 W N hirr h (hS.gSecRho lam hlam1 W N hirr (h⁻¹ * y * h) s) := by
      rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    rw [e, h1]
  rcases hS.irr_gSM lam hlam1 W N hirr _ hinv with hb | ht
  · exact absurd hb hfix
  · ext s
    have hs : s ∈ fixV P' := by rw [ht]; exact Subgroup.mem_top s
    have := hs _ ⟨⟨g, hPG hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    simpa using this

theorem le_card_geS : e ≤ Nat.card (hS.geS lam hlam1 W N hirr) := by
  rw [card_map_eq_relIndex_ker]
  have h1 := hS.le_relIndex_kerRel lam hlam1 _ _ hirr hnc
  refine h1.trans (le_of_eq ?_)
  rw [← Subgroup.relIndex_comap, ← Subgroup.inf_relIndex_right,
    ← Subgroup.inf_relIndex_right (hS.gSecRho lam hlam1 W N hirr).ker]
  congr 1
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker, mem_kerRel,
    hS.gSecRho_eq_one_iff lam hlam1 W N hirr]
  constructor
  · rintro ⟨⟨-, h⟩, hg⟩
    exact ⟨h, hg⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨Subgroup.mem_map_of_mem _ hg, h⟩, hg⟩

theorem card_le_card_geS_mul :
    Nat.card (Sec W N) ≤ Nat.card (hS.geS lam hlam1 W N hirr) *
      Nat.card (fixV (hS.geS lam hlam1 W N hirr)) := by
  rw [← (fixV (hS.geS lam hlam1 W N hirr)).index_mul_card]
  exact Nat.mul_le_mul_right _
    ((hS.index_fixV_geS_le lam hlam1 W N hirr).trans (hS.le_card_geS lam hlam1 W N hirr hnc))

theorem geS_ne_bot (he2 : 2 ≤ e) : hS.geS lam hlam1 W N hirr ≠ ⊥ := by
  intro hbot
  have h := hS.le_card_geS lam hlam1 W N hirr hnc
  rw [hbot, Subgroup.card_bot] at h
  omega

section Comp

variable {H : Type*} [Group H] (φ : H →* ↥G₀) (hφ : Function.Surjective φ)
include hφ

omit hnc in
theorem range_gSecRho_comp :
    ((hS.gSecRho lam hlam1 W N hirr).comp φ).range = (hS.gSecRho lam hlam1 W N hirr).range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ, ← MonoidHom.range_eq_map]

omit hφ in
theorem gSecRho_comp_eq_one {P : Subgroup U₀} (hPG : P ≤ G₀)
    (hPn : G₀ ≤ Subgroup.normalizer (P : Set U₀)) (hP2 : IsPGroup 2 ↥P) {x : H}
    (hx : (φ x : U₀) ∈ P) : (hS.gSecRho lam hlam1 W N hirr).comp φ x = 1 := by
  have e : φ x = ⟨(φ x : U₀), hPG hx⟩ := rfl
  rw [MonoidHom.comp_apply, e]
  exact hS.gSecRho_eq_one_of_mem lam hlam1 W N hirr hnc hPG hPn hP2 hx

omit hnc in
theorem irr_gSecRho_comp (J : Subgroup (Sec W N))
    (hJ : ∀ x : H, ∀ s ∈ J, (hS.gSecRho lam hlam1 W N hirr).comp φ x s ∈ J) : J = ⊥ ∨ J = ⊤ := by
  refine hS.irr_gSM lam hlam1 W N hirr J fun g s hs => ?_
  obtain ⟨x, rfl⟩ := hφ g
  exact hJ x s hs

theorem exists_gSecRho_comp_ne_one :
    ∃ x : H, (φ x : U₀) ∈ Lt ∧ (hS.gSecRho lam hlam1 W N hirr).comp φ x ≠ 1 := by
  obtain ⟨g, hgL, hg1⟩ := hS.exists_lt_gSecRho_ne_one lam hlam1 W N hirr hnc
  obtain ⟨x, rfl⟩ := hφ g
  exact ⟨x, hgL, hg1⟩

end Comp

end EndSetup

end CFSG.Quasithin.MS93.S38E
