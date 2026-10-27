module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Six
public import CFSG.RankThree.GF2n.Stroth78.Sec3Three
public import CFSG.RankThree.GF2n.Stroth78.Sec3FixedVector

import CFSG.GroupTheory.PermFiveNormalElemAbelian
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSym
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Basic
import CFSG.Quasithin.Background.G92Lin
import CFSG.LargeExtraspecial.DW4Burn
import CFSG.LargeExtraspecial.OrthoF2Inverted
import CFSG.LargeExtraspecial.AS35QCoLin
import CFSG.CGT.Timmesfeld75.OddCenter
import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSubA

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem isElemAbelian_Lbar (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    (hconj : IsConj z a) : IsElemAbelian 2 (Lbar S a) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · exact Subtype.ext (commute_of_mem_Lbar S haQ hconj x.2 y.2)
  · exact sq_eq_one_of_mem_Lbar S haQ hconj hx

theorem closure_involutions_Xsub (S : Setting z E F) (a : G) :
    Subgroup.closure {x : ↥(Xsub S a) | x ^ 2 = 1} = ⊤ := by
  have hgen : Subgroup.closure (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) = ⊤ :=
    Subgroup.closure_preimage_eq_top (G := Hbar z) (Eset S a)
  have hle : Subgroup.closure (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) ≤
      Subgroup.closure {x : ↥(Xsub S a) | x ^ 2 = 1} := by
    refine (Subgroup.closure_le (Subgroup.closure {x : ↥(Xsub S a) | x ^ 2 = 1})).mpr ?_
    intro x hx
    apply Subgroup.mem_closure_of_mem
    have hx2 : orderOf (x : Hbar z) = 2 :=
      orderOf_eq_two_of_mem_A2set S (Eset_subset_A2set S a hx)
    change x ^ 2 = 1
    have hxord : orderOf x = 2 := by
      rwa [Subgroup.orderOf_coe] at hx2
    rw [← hxord]
    exact pow_orderOf_eq_one x
  rw [hgen] at hle
  exact top_le_iff.mp hle

theorem odd_card_center_Xsub (S : Setting z E F) (a : G) :
    Odd (Nat.card (Subgroup.center ↥(Xsub S a))) :=
  CFSG.CGT.Timmesfeld75.odd_card_center fun N hN hP => twoCore_Xsub S N hN hP

theorem card_Lbar_le_four_mul_card_inf_centralizer (S : Setting z E F) {a : G}
    {w : ℕ} (h : Sec3Hyp S a w)
    (e : ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a) ≃* Equiv.Perm (Fin 5)) :
    Nat.card (Lbar S a) ≤ 4 * Nat.card
      ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) := by
  have : (Xsub S a).Normal := Xsub_normal S a
  have hLbar : IsElemAbelian 2 (Lbar S a) := isElemAbelian_Lbar S h.mem_Q h.isConj
  exact card_le_four_mul_card_inf_centralizer_of_perm_five
    (closure_involutions_Xsub S a) (odd_card_center_Xsub S a) e
    (fun x hx => hLbar.2 x hx) (fun x hx y hy => IsElemAbelian.comm hLbar hx hy)

omit [Finite G] in
theorem Sec3Hyp.eight_le_two_pow (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) : 8 ≤ 2 ^ w := by
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h.three_le
  norm_num at this ⊢
  exact this

theorem Sec3Hyp.eight_le_card_Lbar (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) : 8 ≤ Nat.card (Lbar S a) :=
  (h.eight_le_two_pow).trans h.two_pow_le_card_Lbar

theorem two_le_card_inf_centralizer_of_card_Lbar_le (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (hL : Nat.card (Lbar S a) ≤ 4 * Nat.card
      ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z)))) :
    2 ≤ Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) := by
  have h8 := h.eight_le_card_Lbar
  omega

theorem even_card_centralizer_of_card_Lbar_le (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (hL : Nat.card (Lbar S a) ≤ 4 * Nat.card
      ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z)))) :
    Even (Nat.card (Subgroup.centralizer (Xsub S a : Set (Hbar z)))) := by
  let K : Subgroup (Hbar z) :=
    Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))
  have hK2 : IsPGroup 2 K :=
    (isElemAbelian_Lbar S h.mem_Q h.isConj).isPGroup.to_le inf_le_left
  obtain ⟨n, hn⟩ := hK2.exists_card_eq
  have h2le : 2 ≤ Nat.card K := two_le_card_inf_centralizer_of_card_Lbar_le S h hL
  have hnpos : 0 < n := by
    by_contra hn0
    push Not at hn0
    have : n = 0 := by omega
    rw [this, pow_zero] at hn
    omega
  have h2dvdK : 2 ∣ Nat.card K := by
    rw [hn, show 2 = 2 ^ 1 from rfl]
    exact Nat.pow_dvd_pow 2 (by omega : 1 ≤ n)
  exact even_iff_two_dvd.mpr (h2dvdK.trans (Subgroup.card_dvd_of_le inf_le_right))

theorem card_inf_centralizer_le_two_of_card_centralizer_eq_six (S : Setting z E F) {a : G}
    {w : ℕ} (h : Sec3Hyp S a w)
    (hC6 : Nat.card (Subgroup.centralizer (Xsub S a : Set (Hbar z))) = 6) :
    Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) ≤ 2 := by
  let K : Subgroup (Hbar z) :=
    Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))
  have hK2 : IsPGroup 2 K :=
    (isElemAbelian_Lbar S h.mem_Q h.isConj).isPGroup.to_le inf_le_left
  obtain ⟨n, hn⟩ := hK2.exists_card_eq
  have hdvd : Nat.card K ∣ 6 := by
    rw [← hC6]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hnle : n ≤ 1 := by
    have hn2 : n ≤ 2 := by
      by_contra hn3
      push Not at hn3
      have h8 : 8 ≤ 2 ^ n := by
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 3 ≤ n)
        norm_num at this ⊢
        exact this
      rw [hn] at hdvd
      have hle6 : 2 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases n
    · omega
    · omega
    · rw [hn] at hdvd
      norm_num at hdvd
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) hnle

theorem card_Lbar_eq_eight_of_card_inf_centralizer_le_two (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (hL : Nat.card (Lbar S a) ≤ 4 * Nat.card
      ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))))
    (hK : Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) ≤ 2) :
    Nat.card (Lbar S a) = 8 := by
  have hle : Nat.card (Lbar S a) ≤ 8 := by nlinarith [hL]
  have hge := h.eight_le_card_Lbar
  omega

theorem w_eq_three_of_card_Lbar_eq_eight (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (h8 : Nat.card (Lbar S a) = 8) : w = 3 := by
  have h2w : 2 ^ w = 2 ^ 3 := by
    have hge : 2 ^ w ≤ Nat.card (Lbar S a) := h.two_pow_le_card_Lbar
    have hle : 2 ^ w ≤ 8 := hge.trans (le_of_eq h8)
    have h8le : 8 ≤ 2 ^ w := h.eight_le_two_pow
    omega
  exact Nat.pow_right_injective (by norm_num) h2w

theorem exists_order_three_involution_centralizer_of_isSymThree (S : Setting z E F) {a : G}
    (hC : Nonempty (Subgroup.centralizer (Xsub S a : Set (Hbar z)) ≃*
      Equiv.Perm (Fin 3))) :
    ∃ ρ : Hbar z, ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) ∧
      orderOf ρ = 3 ∧
      (∃ i : Hbar z, i ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) ∧
        orderOf i = 2 ∧ i * ρ * i⁻¹ = ρ⁻¹) ∧
      (∀ ℓ : Hbar z, ℓ * ρ * ℓ⁻¹ = ρ ∨ ℓ * ρ * ℓ⁻¹ = ρ⁻¹) := by
  let C : Subgroup (Hbar z) := Subgroup.centralizer (Xsub S a : Set (Hbar z))
  have hC' : CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym.IsSymThree C := hC
  obtain ⟨ρ, hρC, hρ1, hρ3, hinv, hi, hclass⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym.symThree_data hC'
  have hCn : C.Normal := by
    have : (Xsub S a).Normal := Xsub_normal S a
    exact Subgroup.normal_centralizer
  refine ⟨ρ, hρC, orderOf_eq_prime hρ3 hρ1, ?_, ?_⟩
  · obtain ⟨i, hiC, hi2, hi1⟩ := hi
    exact ⟨i, hiC, orderOf_eq_prime hi2 hi1, (hinv i hiC hi2 hi1).1⟩
  · intro ℓ
    have hℓC : ℓ * ρ * ℓ⁻¹ ∈ C := hCn.conj_mem ρ hρC ℓ
    have hℓ3 : (ℓ * ρ * ℓ⁻¹) ^ 3 = 1 := by rw [conj_pow, hρ3]; group
    have hℓ1 : ℓ * ρ * ℓ⁻¹ ≠ 1 := by
      intro hh
      apply hρ1
      calc
        ρ = ℓ⁻¹ * (ℓ * ρ * ℓ⁻¹) * ℓ := by group
        _ = 1 := by rw [hh]; group
    exact hclass (ℓ * ρ * ℓ⁻¹) hℓC hℓ3 hℓ1

theorem rhoLin_pow_orderOf_eq_one (S : Setting z E F) (x : Hbar z) :
    (rhoLin S x) ^ orderOf x = 1 := by
  rw [← orderOf_rhoLin]
  exact pow_orderOf_eq_one _

theorem finrank_commSpace_eq_four_of_orderOf_eq_five (S : Setting z E F) {f : Hbar z}
    (hV6 : finrank (ZMod 2) (Additive (QbarOf S)) = 6) (hf5 : orderOf f = 5) :
    finrank (ZMod 2) (commSpace (rhoLin S f)) = 4 := by
  have : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  let V := Additive (QbarOf S)
  let gf : V ≃ₗ[ZMod 2] V := rhoLin S f
  let φ : (V ≃ₗ[ZMod 2] V) →* Module.End (ZMod 2) V :=
    { toFun := fun e => (e : V →ₗ[ZMod 2] V)
      map_one' := LinearEquiv.coe_toLinearMap_one
      map_mul' := fun x y => LinearEquiv.coe_toLinearMap_mul }
  have hgf5' : ((gf : V →ₗ[ZMod 2] V) ^ 5) = 1 := by
    change (φ gf) ^ 5 = 1
    have h := map_pow φ gf 5
    rw [show gf ^ 5 = 1 from by simpa [gf, hf5] using rhoLin_pow_orderOf_eq_one S f,
      map_one] at h
    exact h.symm
  have hU : ∀ u ∈ commSpace gf, (gf : V →ₗ[ZMod 2] V) u ∈ commSpace gf := by
    intro u hu
    change rhoLin S f u ∈ commSpace (rhoLin S f)
    exact rhoLin_mem_commSpace_of_commute (S := S) (β := f) (ℓ := f) rfl hu
  have hfix : ∀ u ∈ commSpace gf, (gf : V →ₗ[ZMod 2] V) u = u → u = 0 := by
    intro u hu hgu
    have hmem : u ∈ fixSpace gf ⊓ commSpace gf := ⟨mem_fixSpace.mpr hgu, hu⟩
    rw [CFSG.LargeExtraspecial.AS35QCo.fixSpace_inf_commSpace (g := gf) (n := 5)
      (by norm_num) (by simpa [gf, hf5] using rhoLin_pow_orderOf_eq_one S f)] at hmem
    simpa using hmem
  have h4dvd : 4 ∣ finrank (ZMod 2) (commSpace gf) :=
    CFSG.EvenSporadicStandard.HNRecog.Fpf.four_dvd_finrank_of_fixedFree
      (gf : V →ₗ[ZMod 2] V) hgf5' (commSpace gf) hU hfix
  have hdimle : finrank (ZMod 2) (commSpace gf) ≤ 6 := by
    have := Submodule.finrank_mono (le_top : commSpace gf ≤ ⊤)
    rwa [finrank_top, hV6] at this
  have hne : finrank (ZMod 2) (commSpace gf) ≠ 0 := by
    intro h0
    have hfixdim : finrank (ZMod 2) (fixSpace gf) = finrank (ZMod 2) V := by
      have hsum := finrank_commSpace_add_finrank_fixSpace gf
      omega
    have htop : fixSpace gf = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by simpa using hfixdim)
    have hgf1 : gf = 1 := CFSG.LargeExtraspecial.DW.W4.eq_one_of_fixSpace_eq_top htop
    have h1 : orderOf gf = 1 := by rw [hgf1]; exact orderOf_one
    rw [show orderOf gf = 5 from by rw [orderOf_rhoLin, hf5]] at h1
    omega
  obtain ⟨k, hk⟩ := h4dvd
  have hkpos : 0 < k := Nat.pos_of_ne_zero fun hk0 => hne (by rw [hk, hk0, mul_zero])
  have hk1 : k = 1 := by omega
  rw [hk, hk1, mul_one]

theorem eq_one_on_commSpace_of_conj_inv (S : Setting z E F) {f ρ i : Hbar z}
    (hρf : ρ * f = f * ρ) (hρ3 : orderOf ρ = 3)
    (hρi : i * ρ * i⁻¹ = ρ⁻¹)
    (hi_triv : ∀ v ∈ commSpace (rhoLin S f), rhoLin S i v = v) :
    ∀ v ∈ commSpace (rhoLin S f), rhoLin S ρ v = v := by
  let V := Additive (QbarOf S)
  let gr : V ≃ₗ[ZMod 2] V := rhoLin S ρ
  let gi : V ≃ₗ[ZMod 2] V := rhoLin S i
  have hconj : gi * gr * gi⁻¹ = gr⁻¹ := by
    have h := congrArg (rhoLin S) hρi
    simpa [gr, gi, rhoLin_mul, rhoLin_inv] using h
  have hgrVf : ∀ u ∈ commSpace (rhoLin S f), gr u ∈ commSpace (rhoLin S f) := by
    intro u hu
    change rhoLin S ρ u ∈ commSpace (rhoLin S f)
    exact rhoLin_mem_commSpace_of_commute (S := S) (β := f) (ℓ := ρ) hρf hu
  have hgr3 : gr ^ 3 = 1 := by
    simpa [gr, hρ3] using rhoLin_pow_orderOf_eq_one S ρ
  intro v hv
  have hgiv : gi v = v := hi_triv v hv
  have hgiinv : gi⁻¹ v = v := by
    calc
      gi⁻¹ v = gi⁻¹ (gi v) := by rw [hgiv]
      _ = v := gi.symm_apply_apply v
  have h1 : gr v = gr⁻¹ v := by
    have h : gi (gr (gi⁻¹ v)) = gr⁻¹ v := by
      have := congrArg (fun h : V ≃ₗ[ZMod 2] V => h v) hconj
      simpa only [LinearEquiv.mul_apply] using this
    rw [hgiinv] at h
    rw [hi_triv (gr v) (hgrVf v hv)] at h
    exact h
  have h2 : gr (gr v) = v := by
    rw [h1]
    exact gr.apply_symm_apply v
  have h3 : gr (gr (gr v)) = gr v := by rw [h2]
  have h4 : gr (gr (gr v)) = v := by
    have h := congrArg (fun h : V ≃ₗ[ZMod 2] V => h v) hgr3
    simpa [pow_three, LinearEquiv.mul_apply] using h
  rw [h4] at h3
  exact h3.symm

theorem involution_trivial_on_commSpace_of_prime (S : Setting z E F) {x g : Hbar z} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hx : orderOf x = p) (hg : g * g = 1)
    (hcomm : g * x = x * g)
    (hk : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ finrank (ZMod 2) (commSpace (rhoLin S x)) →
      ¬ p ∣ 2 ^ k - 1) :
    ∀ v ∈ commSpace (rhoLin S x), rhoLin S g v = v := by
  have : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have : Finite (Additive (QbarOf S)) := inferInstance
  let V := Additive (QbarOf S)
  let gx : V ≃ₗ[ZMod 2] V := rhoLin S x
  let gg : V ≃ₗ[ZMod 2] V := rhoLin S g
  have hxp : gx ^ p = 1 := by simpa [gx, hx] using rhoLin_pow_orderOf_eq_one S x
  have hgg2 : gg * gg = 1 := by
    have h := congrArg (rhoLin S) hg
    rw [show rhoLin S (1 : Hbar z) = 1 from by simp] at h
    simpa [gg, rhoLin_mul] using h
  have hxT : ∀ v ∈ commSpace gx, gx v ∈ commSpace gx := by
    intro v hv
    change rhoLin S x v ∈ commSpace (rhoLin S x)
    exact rhoLin_mem_commSpace_of_commute (S := S) (β := x) (ℓ := x) rfl hv
  have hcommlin : gg * gx = gx * gg := by
    have h := congrArg (rhoLin S) hcomm
    simpa [gx, gg, rhoLin_mul] using h
  have hcT : ∀ v ∈ commSpace gx, gg v ∈ commSpace gx := by
    intro v hv
    change rhoLin S g v ∈ commSpace (rhoLin S x)
    exact rhoLin_mem_commSpace_of_commute (S := S) (β := x) (ℓ := g) hcomm hv
  have hfp : ∀ v ∈ commSpace gx, gx v = v → v = 0 := by
    intro v hv hgv
    have hmem : v ∈ fixSpace gx ⊓ commSpace gx := ⟨mem_fixSpace.mpr hgv, hv⟩
    rw [CFSG.LargeExtraspecial.AS35QCo.fixSpace_inf_commSpace (g := gx) (n := p)
      (hp.odd_of_ne_two hp2) hxp] at hmem
    simpa using hmem
  exact CFSG.Quasithin.G92.invol_trivial (x := gx) (c := gg) (p := p) hp hxp hgg2 hcommlin
    (commSpace gx) hxT hcT hfp hk

theorem rhoLin_eq_one_on_commSpace_of_mem_Rbar (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    {ρ r : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)))
    (hρ3 : orderOf ρ = 3) (hr : r ∈ Rbar S a)
    (hdim : finrank (ZMod 2) (commSpace (rhoLin S ρ)) ≤ 2) :
    ∀ v ∈ commSpace (rhoLin S ρ), rhoLin S r v = v := by
  have hrL : r ∈ Lbar S a := Rbar_le_Lbar S a hr
  have hgs2 : r * r = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj hrL
  have hcomm : r * ρ = ρ * r :=
    Subgroup.mem_centralizer_iff.mp hρC r (h.Rbar_le_Xsub hr)
  have hk : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ finrank (ZMod 2) (commSpace (rhoLin S ρ)) →
      ¬ 3 ∣ 2 ^ k - 1 :=
    CFSG.Quasithin.G92.no_dvd_three (by omega : finrank (ZMod 2) (commSpace (rhoLin S ρ)) ≤ 3)
  exact involution_trivial_on_commSpace_of_prime S (p := 3) (by norm_num) (by norm_num)
    hρ3 hgs2 hcomm hk

theorem rhoLin_trivial_on_commSpace_of_mem_Rbar (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)))
    (hρ3 : orderOf ρ = 3)
    (hdim : finrank (ZMod 2) (commSpace (rhoLin S ρ)) ≤ 2) :
    ∀ r' ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r'), rhoLin S ρ v = v := by
  have : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  intro r' hr' v hv
  have hcomm : r' * ρ = ρ * r' :=
    Subgroup.mem_centralizer_iff.mp hρC r' (h.Rbar_le_Xsub hr')
  have htriv := rhoLin_eq_one_on_commSpace_of_mem_Rbar S h hρC hρ3 hr' hdim
  have hcommlin : rhoLin S r' * rhoLin S ρ = rhoLin S ρ * rhoLin S r' := by
    simpa [rhoLin_mul] using congrArg (rhoLin S) hcomm
  have hle := CFSG.LargeExtraspecial.commSpace_le_fixSpace_of_commute
    (ω := rhoLin S ρ) (y := rhoLin S r')
    (by rw [orderOf_rhoLin, hρ3]; norm_num) hcommlin htriv
  exact mem_fixSpace.mp (hle hv)

theorem rho_fixes_aVec (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)))
    (hρ3 : orderOf ρ = 3)
    (hdim : finrank (ZMod 2) (commSpace (rhoLin S ρ)) ≤ 2) :
    rhoLin S ρ (aVec S h.mem_Q) = aVec S h.mem_Q := by
  obtain ⟨r, hrR, hr1⟩ :=
    (Subgroup.bot_or_exists_ne_one (Rbar S a)).resolve_left h.Rbar_ne_bot
  have haV : aVec S h.mem_Q ∈ commSpace (rhoLin S r) := by
    simpa [aVec, rhoLin] using aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj
      h.not_mem_ZQ h.mem_Qa h.centerIn_Qa_not_le_Q hrR hr1
  exact rhoLin_trivial_on_commSpace_of_mem_Rbar S h hρC hρ3 hdim r hrR (aVec S h.mem_Q) haV

theorem eq_bot_of_le_zpowers_of_orderOf_eq_three {ρ : Hbar z} (hρ3 : orderOf ρ = 3) :
    ∀ P : Subgroup (Hbar z), P ≤ Subgroup.zpowers ρ → IsPGroup 2 P →
      Subgroup.zpowers ρ ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥ := by
  have : Finite (Hbar z) := inferInstance
  have hYcard : Nat.card (Subgroup.zpowers ρ) = 3 := by rw [Nat.card_zpowers, hρ3]
  intro P hPY hP2 _
  have hdvd : Nat.card P ∣ 3 := by
    have := Subgroup.card_dvd_of_le hPY
    rwa [hYcard] at this
  exact CFSG.Quasithin.F6.GoldAmL2T.eq_bot_of_card_dvd_three
    (P := P) (K := P) hP2 le_rfl hdvd

theorem zpowers_commute_Rbar (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z))) :
    ∀ y ∈ Subgroup.zpowers ρ, ∀ r ∈ Rbar S a, y * r = r * y := by
  have hρcent : ρ ∈ Subgroup.centralizer (Rbar S a : Set (Hbar z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_iff.mp hρC r (h.Rbar_le_Xsub hr)
  intro y hy r hr
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.zpowers_le.mpr hρcent hy) r hr).symm

theorem zpowers_trivial_on_commSpace_Rbar (S : Setting z E F) {a : G}
    {ρ : Hbar z}
    (htriv : ∀ r' ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r'), rhoLin S ρ v = v) :
    ∀ y ∈ Subgroup.zpowers ρ, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r),
      rhoLin S y v = v := by
  intro y hy r hr v hv
  let K : Subgroup (Hbar z) :=
    (fixingSubgroup (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))
      (commSpace (rhoLin S r) : Set (Additive (QbarOf S)))).comap (rhoGL S)
  have hρK : ρ ∈ K := by
    change (rhoGL S) ρ ∈ fixingSubgroup _ _
    refine (mem_fixingSubgroup_iff (Additive (QbarOf S) ≃ₗ[ZMod 2]
      Additive (QbarOf S))).mpr ?_
    intro w hw
    simpa [rhoGL, LinearEquiv.smul_def] using htriv r hr w hw
  have hYK : Subgroup.zpowers ρ ≤ K := Subgroup.zpowers_le.mpr hρK
  have hyK : (rhoGL S) y ∈ fixingSubgroup _ _ := hYK hy
  have := (mem_fixingSubgroup_iff (Additive (QbarOf S) ≃ₗ[ZMod 2]
    Additive (QbarOf S))).mp hyK v hv
  simpa [rhoGL, LinearEquiv.smul_def] using this

theorem aVec_not_mem_iSup_commSpace_zpowers (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {ρ : Hbar z} (hρ3 : orderOf ρ = 3)
    (haV : rhoLin S ρ (aVec S h.mem_Q) = aVec S h.mem_Q) :
    aVec S h.mem_Q ∉ (⨆ y ∈ Subgroup.zpowers ρ, commSpace (rhoLin S y)) := by
  have hYodd : Odd (Nat.card (Subgroup.zpowers ρ)) := by
    rw [Nat.card_zpowers, hρ3]
    norm_num
  let K : Subgroup (Hbar z) :=
    (MulAction.stabilizer (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))
      (aVec S h.mem_Q)).comap (rhoGL S)
  have hρK : ρ ∈ K := by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    simpa [rhoGL, LinearEquiv.smul_def] using haV
  have hYK : Subgroup.zpowers ρ ≤ K := Subgroup.zpowers_le.mpr hρK
  have hfix : ∀ y ∈ Subgroup.zpowers ρ, rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q := by
    intro y hy
    have := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_comap.mp (hYK hy))
    simpa [rhoGL, LinearEquiv.smul_def] using this
  exact aVec_not_mem_iSup_commSpace_of_odd S h hYodd hfix

theorem Lbar_le_normalizer_zpowers (S : Setting z E F) {a : G} {ρ : Hbar z}
    (hclass : ∀ ℓ : Hbar z, ℓ * ρ * ℓ⁻¹ = ρ ∨ ℓ * ρ * ℓ⁻¹ = ρ⁻¹) :
    Lbar S a ≤ Subgroup.normalizer (Subgroup.zpowers ρ : Set (Hbar z)) := by
  rw [Subgroup.le_normalizer_iff]
  intro ℓ hℓ y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow]
  have hℓρY : ℓ * ρ * ℓ⁻¹ ∈ Subgroup.zpowers ρ := by
    rcases hclass ℓ with h | h
    · rw [h]; exact Subgroup.mem_zpowers ρ
    · rw [h]; exact (Subgroup.zpowers ρ).inv_mem (Subgroup.mem_zpowers ρ)
  exact Subgroup.zpow_mem (K := Subgroup.zpowers ρ) hℓρY k

theorem false_of_h217_hypotheses (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)))
    (hρ3 : orderOf ρ = 3)
    (hclass : ∀ ℓ : Hbar z, ℓ * ρ * ℓ⁻¹ = ρ ∨ ℓ * ρ * ℓ⁻¹ = ρ⁻¹)
    (htriv : ∀ r' ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r'), rhoLin S ρ v = v)
    (haV : rhoLin S ρ (aVec S h.mem_Q) = aVec S h.mem_Q) : False := by
  have hYodd : Odd (Nat.card (Subgroup.zpowers ρ)) := by
    rw [Nat.card_zpowers, hρ3]
    norm_num
  have hYoc : CFSG.GroupTheory.oddOrderClosure (Subgroup.zpowers ρ) = Subgroup.zpowers ρ :=
    CFSG.GroupTheory.oddOrderClosure_eq_self_of_odd_card _ hYodd
  have hY2 := eq_bot_of_le_zpowers_of_orderOf_eq_three (z := z) hρ3
  have hYcomm := zpowers_commute_Rbar S h hρC
  have hYtriv := zpowers_trivial_on_commSpace_Rbar (S := S) (a := a) htriv
  have hYaVec := aVec_not_mem_iSup_commSpace_zpowers S h hρ3 haV
  have hLnorm := Lbar_le_normalizer_zpowers (S := S) (a := a) hclass
  rcases h217 (Subgroup.zpowers ρ) hYoc hY2 hYcomm hYtriv hYaVec hLnorm with hR | hYbot
  · exact h.Rbar_ne_bot hR
  · have hρ1 : ρ ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hρ3
      omega
    apply hρ1
    have hmem : ρ ∈ Subgroup.zpowers ρ := Subgroup.mem_zpowers ρ
    rw [hYbot] at hmem
    simpa using hmem

theorem exists_order_three_data_of_card_Lbar_le (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (hL : Nat.card (Lbar S a) ≤ 4 * Nat.card
      ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z)))) :
    ∃ ρ : Hbar z, ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) ∧
      orderOf ρ = 3 ∧
      (∃ i : Hbar z, i ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) ∧
        orderOf i = 2 ∧ i * ρ * i⁻¹ = ρ⁻¹) ∧
      (∀ ℓ : Hbar z, ℓ * ρ * ℓ⁻¹ = ρ ∨ ℓ * ρ * ℓ⁻¹ = ρ⁻¹) ∧
      finrank (ZMod 2) (Additive (QbarOf S)) = 6 := by
  let C : Subgroup (Hbar z) := Subgroup.centralizer (Xsub S a : Set (Hbar z))
  have heven : Even (Nat.card C) := even_card_centralizer_of_card_Lbar_le S h hL
  obtain ⟨eC⟩ := nonempty_mulEquiv_perm_three_centralizer_Xsub S h h217 heven
  have hC6 : Nat.card C = 6 := by
    rw [Nat.card_congr eC.toEquiv, Nat.card_perm]
    norm_num
  have hKle : Nat.card ↥(Lbar S a ⊓ C) ≤ 2 :=
    card_inf_centralizer_le_two_of_card_centralizer_eq_six S h hC6
  have hLbar8 : Nat.card (Lbar S a) = 8 :=
    card_Lbar_eq_eight_of_card_inf_centralizer_le_two S h hL hKle
  have hw3 : w = 3 := w_eq_three_of_card_Lbar_eq_eight S h hLbar8
  have hV6 : finrank (ZMod 2) (Additive (QbarOf S)) = 6 := by
    rw [finrank_QbarOf_eq_two_mul S h.card_F, hw3]
  obtain ⟨ρ, hρC, hρ3, ⟨i, hiC, hi2, hiρ⟩, hclass⟩ :=
    exists_order_three_involution_centralizer_of_isSymThree S ⟨eC⟩
  exact ⟨ρ, hρC, hρ3, ⟨i, hiC, hi2, hiρ⟩, hclass, hV6⟩

theorem false_of_card_Lbar_le_of_orderOf_eq_five (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (hL : Nat.card (Lbar S a) ≤ 4 * Nat.card
      ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))))
    {f : Hbar z} (hfX : f ∈ Xsub S a) (hf5 : orderOf f = 5) : False := by
  obtain ⟨ρ, hρC, hρ3, ⟨i, hiC, hi2, hiρ⟩, hclass, hV6⟩ :=
    exists_order_three_data_of_card_Lbar_le S h h217 hL
  have hfρ : f * ρ = ρ * f := Subgroup.mem_centralizer_iff.mp hρC f hfX
  have hfi : f * i = i * f := Subgroup.mem_centralizer_iff.mp hiC f hfX
  have hi_sq : i * i = 1 := by rw [← pow_two, ← hi2, pow_orderOf_eq_one]
  have hVf4 : finrank (ZMod 2) (commSpace (rhoLin S f)) = 4 :=
    finrank_commSpace_eq_four_of_orderOf_eq_five S hV6 hf5
  have hk5 : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ finrank (ZMod 2) (commSpace (rhoLin S f)) →
      ¬ 5 ∣ 2 ^ k - 1 :=
    CFSG.Quasithin.G92.no_dvd_five (by omega : finrank (ZMod 2) (commSpace (rhoLin S f)) ≤ 7)
  have hgi_triv : ∀ v ∈ commSpace (rhoLin S f), rhoLin S i v = v :=
    involution_trivial_on_commSpace_of_prime S (p := 5) (by norm_num) (by norm_num)
      hf5 hi_sq hfi.symm hk5
  have hρtriv : ∀ v ∈ commSpace (rhoLin S f), rhoLin S ρ v = v :=
    eq_one_on_commSpace_of_conj_inv S hfρ.symm hρ3 hiρ hgi_triv
  have hle_fix : commSpace (rhoLin S ρ) ≤ fixSpace (rhoLin S f) := by
    have hcommlin : rhoLin S ρ * rhoLin S f = rhoLin S f * rhoLin S ρ := by
      simpa [rhoLin_mul] using congrArg (rhoLin S) hfρ.symm
    exact CFSG.LargeExtraspecial.commSpace_le_fixSpace_of_commute
      (ω := rhoLin S f) (y := rhoLin S ρ)
      (by rw [orderOf_rhoLin, hf5]; norm_num) hcommlin hρtriv
  have hfixf2 : finrank (ZMod 2) (fixSpace (rhoLin S f)) = 2 := by
    have hsum := finrank_commSpace_add_finrank_fixSpace (rhoLin S f)
    omega
  have hdimV1 : finrank (ZMod 2) (commSpace (rhoLin S ρ)) ≤ 2 :=
    (Submodule.finrank_mono hle_fix).trans_eq hfixf2
  have htriv : ∀ r' ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r'), rhoLin S ρ v = v :=
    rhoLin_trivial_on_commSpace_of_mem_Rbar S h hρC hρ3 hdimV1
  have haV : rhoLin S ρ (aVec S h.mem_Q) = aVec S h.mem_Q :=
    rho_fixes_aVec S h hρC hρ3 hdimV1
  exact false_of_h217_hypotheses S h h217 hρC hρ3 hclass htriv haV

theorem stroth78_42 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    IsEmpty ((↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) ≃* Equiv.Perm (Fin 5)) := by
  refine ⟨fun e => ?_⟩
  have : Fintype ↥(Xsub S a) := Fintype.ofFinite _
  have h5quot : 5 ∣ Nat.card (↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    norm_num
  have h5X : 5 ∣ Nat.card ↥(Xsub S a) :=
    h5quot.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥(Xsub S a)))
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5X' : 5 ∣ Fintype.card ↥(Xsub S a) := by
    simpa [Nat.card_eq_fintype_card] using h5X
  obtain ⟨f, hf5⟩ := exists_prime_orderOf_dvd_card (G := ↥(Xsub S a)) 5 h5X'
  have hfX : (f : Hbar z) ∈ Xsub S a := f.2
  have hf5' : orderOf (f : Hbar z) = 5 := by rwa [Subgroup.orderOf_coe]
  exact false_of_card_Lbar_le_of_orderOf_eq_five S h h217
    (card_Lbar_le_four_mul_card_inf_centralizer S h e) hfX hf5'

end CFSG.RankThree.GF2n.Stroth78
