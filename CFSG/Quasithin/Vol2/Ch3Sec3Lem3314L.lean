module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314J
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314K
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314E

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.L3319
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

namespace Sett

variable {t : G} (e : Sett T M L t)
include e

theorem iff_cvPlus [IsMulCommutative ↥(vPlus L T)] {x : ↥(L ⊔ T)} (hxT : (x : G) ∈ T)
    (v : ↥(vPlus L T)) :
    v ∈ cvPlus L T ↔ conjOf (vPlus L T) (L ⊔ T) e.hX x v ∈ cvPlus L T := by
  have hM : conjSub (x : G) (mPlus L T) = mPlus L T :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure_right L T hxT)
  have hC : conjSub (x : G) (Subgroup.centralizer (mPlus L T : Set G)) =
      Subgroup.centralizer (mPlus L T : Set G) := by
    rw [← conjSub_centralizer, hM]
  exact mem_subgroupOf_iff_conj (e.hX x.2) hC v

theorem iff_tildeComm [IsMulCommutative ↥(vPlus L T)] {x : ↥(L ⊔ T)} (hxT : (x : G) ∈ T)
    (hxL : conjSub (x : G) L = L) (v : ↥(vPlus L T)) :
    v ∈ tildeComm L T L ↔ conjOf (vPlus L T) (L ⊔ T) e.hX x v ∈ tildeComm L T L := by
  have hV : conjSub (x : G) (vPlus L T) = vPlus L T := F7.conjSub_eq_of_mem_normalizer (e.hX x.2)
  have hVL : conjSub (x : G) ⁅vPlus L T, L⁆ = ⁅vPlus L T, L⁆ := by
    rw [← conjSub_commutator, hV, hxL]
  exact iff_sup_of_iff (conjOf (vPlus L T) (L ⊔ T) e.hX x)
    (fun w => mem_subgroupOf_iff_conj (e.hX x.2) hVL w) (fun w => e.iff_cvPlus hxT w) v

theorem card_autOn_inf : Nat.card ↥(autOn (T ⊓ L) (vPlus L T)) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' (subnormal_of_mem_cComp e.s.mem_cComp)
      e.s.isSylowTwoOf
  obtain ⟨hle, h2, hodd⟩ := isSylowTwoOf_autOn (le_sup_left.trans e.hX) hS
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hmul := Subgroup.card_mul_index ((autOn (T ⊓ L) (vPlus L T)).subgroupOf
    (autOn L (vPlus L T)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hn, e.card] at hmul
  have h1 : n ≤ 7 := by
    by_contra h1
    have h3 : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ n ≤ 168 := Nat.le_of_dvd (by norm_num) ⟨_, hmul.symm⟩
    have h5 := h3.trans h4
    norm_num at h5
  rw [hn]
  interval_cases n <;> norm_num at hmul ⊢ <;> omega

omit [Finite G] e in
theorem autOn_inf_le : autOn (T ⊓ L) (vPlus L T) ≤ autOn L (vPlus L T) := by
  rintro _ ⟨n, hn, rfl⟩
  exact ⟨n, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hn).2, rfl⟩

theorem conjSub_autOn_inf {x : ↥(L ⊔ T)} (hxT : (x : G) ∈ T) (hxL : conjSub (x : G) L = L) :
    conjSub (conjOf (vPlus L T) (L ⊔ T) e.hX x) (autOn (T ⊓ L) (vPlus L T)) =
      autOn (T ⊓ L) (vPlus L T) := by
  rw [conjSub_autOn, conjSub_inf, hxL, F7.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hxT)]

end Sett

theorem insp3_3_14B_of (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) :
    Insp3_3_14B := by
  intro G _ _ T M L s hT hab hc hP
  obtain ⟨t, ht, htn, hM, hcomm, hbot, -, -, -, hmod⟩ := hc
  have hcard : Nat.card ↥(autOn L (vPlus L T)) = 168 := by
    obtain ⟨e⟩ := nonempty_equiv_of_isPSL hP
    rw [Nat.card_congr e.toEquiv, card_L3Γ]
  have e : Sett T M L t := ⟨s, ht, htn, hM, hcomm, hbot, h37, h38, hcard⟩
  obtain ⟨k, hk, ⟨c₀⟩⟩ := exists_coord hP hmod
  obtain ⟨c, hcS⟩ := c₀.exists_imgSub_bSub Sett.autOn_inf_le e.card_autOn_inf
  set ρ := conjOf (vPlus L T) (L ⊔ T) e.hX with hρ
  set r : ↥(L ⊔ T) := ⟨t⁻¹, e.tinv_mem⟩ with hr
  have hP1 : c.imgSub (L3.ptSub e1) =
      stabIn (autOn L (vPlus L T)) (fixMod (tildeComm L T L) (cvPlus L T)
        (autOn (T ⊓ L) (vPlus L T))) := by
    rw [← hcS]
    exact (c.stabIn_fixMod_bSub hk).symm
  have hP2 : c.imgSub (L3.stabSub P12) =
      stabIn (autOn L (vPlus L T)) (fixMod (tildeComm L T L) (cvPlus L T)
        (cenSub (autOn (T ⊓ L) (vPlus L T)))) := by
    rw [← hcS]
    exact (c.stabIn_fixMod_cen hk).symm
  have hdich := e.dich
  have hL2 : conjSub (ρ r) (autOn L (vPlus L T)) = autOn (CFSG.conjugate L t) (vPlus L T) :=
    e.conjSub_tinv
  have hlift : ∀ a ∈ autOn L (vPlus L T), ∃ x : ↥(L ⊔ T), (x : G) ∈ L ∧ ρ x = a :=
    fun a ha => exists_conjOf_eq e.hX le_sup_left ha
  have hcan : ∀ x : ↥(L ⊔ T), (x : G) ∈ T →
      conjSub (ρ x) (autOn L (vPlus L T)) = autOn L (vPlus L T) →
      (∀ v, v ∈ tildeComm L T L ↔ ρ x v ∈ tildeComm L T L) ∧
        (∀ v, v ∈ cvPlus L T ↔ ρ x v ∈ cvPlus L T) ∧
        conjSub (ρ x) (autOn (T ⊓ L) (vPlus L T)) = autOn (T ⊓ L) (vPlus L T) := by
    intro x hxT hx
    have hxL := e.conjSub_L_eq hx
    exact ⟨e.iff_tildeComm hxT hxL, e.iff_cvPlus hxT, e.conjSub_autOn_inf hxT hxL⟩
  have six1 : SixHyp T L ρ (autOn (CFSG.conjugate L t) (vPlus L T)) c r (L3.ptSub e1) c1 :=
    { TX := le_sup_right
      rT := T.inv_mem ht
      hL2 := hL2
      hbot := hbot
      comm := hcomm
      dich := hdich
      liftL := hlift
      can := fun x hxT hx => by
        obtain ⟨hU, hZ, hS⟩ := hcan x hxT hx
        rw [hP1]
        exact conjSub_stabIn_fixMod hx hS hU hZ
      ker2 := e.exists_pow_eq_one
      pow := e.exists_pow_eq_mul
      hBQ := bSub_le_ptSub
      hcQ := c1_mem
      hcos := hcos₁
      hsyl := syl1_check
      hdist := hdist₁
      hperm := perm1_check
      hker := ker1_check
      hz := zB_mem_sylOf_c1 }
  have six2 : SixHyp T L ρ (autOn (CFSG.conjugate L t) (vPlus L T)) c r (L3.stabSub P12) c2 :=
    { TX := le_sup_right
      rT := T.inv_mem ht
      hL2 := hL2
      hbot := hbot
      comm := hcomm
      dich := hdich
      liftL := hlift
      can := fun x hxT hx => by
        obtain ⟨hU, hZ, hS⟩ := hcan x hxT hx
        rw [hP2]
        exact conjSub_stabIn_fixMod hx (by rw [conjSub_cenSub, hS]) hU hZ
      ker2 := e.exists_pow_eq_one
      pow := e.exists_pow_eq_mul
      hBQ := bSub_le_stabSub
      hcQ := c2_mem
      hcos := hcos₂
      hsyl := syl2_check
      hdist := hdist₂
      hperm := perm2_check
      hker := ker2_check
      hz := zB_mem_sylOf_c2 }
  obtain ⟨H₁, hH₁X, hH₁, hq₁, hP₁⟩ := six1.exists_wreath
  obtain ⟨H₂, hH₂X, hH₂, hq₂, hP₂⟩ := six2.exists_wreath
  refine ⟨H₁, H₂, hH₁, hH₂, hq₁, hq₂, le_antisymm (sup_le hH₁X hH₂X) ?_⟩
  refine sup_le ?_ (hH₁.1.trans le_sup_left)
  have hsup : c.imgSub (L3.ptSub e1) ⊔ c.imgSub (L3.stabSub P12) = autOn L (vPlus L T) := by
    rw [← c.imgSub_sup, sup_parabolics, c.imgSub_top]
  have key : ∀ a ∈ c.imgSub (L3.ptSub e1) ⊔ c.imgSub (L3.stabSub P12),
      ∃ y : ↥(L ⊔ T), (y : G) ∈ H₁ ⊔ H₂ ∧ ρ y = a := by
    intro a ha
    rw [Subgroup.sup_eq_closure] at ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · obtain ⟨y, -, hy⟩ := hlift a (c.imgSub_le _ ha)
        exact ⟨y, Subgroup.mem_sup_left (hP₁ y (hy ▸ ha)), hy⟩
      · obtain ⟨y, -, hy⟩ := hlift a (c.imgSub_le _ ha)
        exact ⟨y, Subgroup.mem_sup_right (hP₂ y (hy ▸ ha)), hy⟩
    | one => exact ⟨1, (H₁ ⊔ H₂).one_mem, map_one ρ⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨y, hy, rfl⟩ := iha
      obtain ⟨z, hz, rfl⟩ := ihb
      exact ⟨y * z, (H₁ ⊔ H₂).mul_mem hy hz, map_mul ρ y z⟩
    | inv a _ iha =>
      obtain ⟨y, hy, rfl⟩ := iha
      exact ⟨y⁻¹, (H₁ ⊔ H₂).inv_mem hy, map_inv ρ y⟩
  intro l hl
  set x : ↥(L ⊔ T) := ⟨l, Subgroup.mem_sup_left hl⟩
  have hxL : ρ x ∈ autOn L (vPlus L T) := conjOf_mem_autOn e.hX hl
  rw [← hsup] at hxL
  obtain ⟨y, hy, hyx⟩ := key (ρ x) hxL
  have hker : ((y⁻¹ * x : ↥(L ⊔ T)) : G) ∈ H₁ := by
    refine hP₁ _ ?_
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
    exact Subgroup.one_mem _
  have : l = (y : G) * ((y⁻¹ * x : ↥(L ⊔ T)) : G) := by simp [x]
  rw [this]
  exact (H₁ ⊔ H₂).mul_mem hy (Subgroup.mem_sup_left hker)

end CFSG.Quasithin.H13.Ins314
