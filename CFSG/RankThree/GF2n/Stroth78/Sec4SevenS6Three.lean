module


import CFSG.RankThree.GF2n.Stroth78.Sec3Seven
import CFSG.RankThree.GF2n.Stroth78.Sec3Five
import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedSq
import CFSG.Quasithin.Background.G92Lin
import CFSG.LargeExtraspecial.OrthoF2Inverted
import CFSG.LargeExtraspecial.DW4Burn
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Perm
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Struct
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeAct
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open Module Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem rhoLin_aVec_eq_of_mem_normalizer_Lbar (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {x : Hbar z} (hx : x ∈ Subgroup.normalizer (Lbar S a : Set (Hbar z))) :
    rhoLin S x (aVec S h.mem_Q) = aVec S h.mem_Q := by
  have hT : ∀ α ∈ Tset S a, ∀ β ∈ Tset S a, α * β ∉ Tset S a :=
    fun α hα β hβ => stroth78_35 S h h217 h3 hα hβ
  have hLã : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (aVec S h.mem_Q) = aVec S h.mem_Q := fun ℓ hℓ =>
    rhoLin_apply_eq_of_mem_fixSpaceOf S (Sec3Hyp.aVec_mem_fixSpaceOf h) hℓ
  have hfix : ∀ ℓ ∈ Lbar S a, rhoLin S ℓ (rhoLin S x (aVec S h.mem_Q)) =
      rhoLin S x (aVec S h.mem_Q) := by
    intro ℓ hℓ
    have hℓ' : x⁻¹ * ℓ * x ∈ Lbar S a := by
      have hxinv := (Subgroup.normalizer (Lbar S a : Set (Hbar z))).inv_mem hx
      have := (Subgroup.mem_normalizer_iff.mp hxinv ℓ).mp hℓ
      simpa using this
    have h1 : ℓ = x * (x⁻¹ * ℓ * x) * x⁻¹ := by group
    calc rhoLin S ℓ (rhoLin S x (aVec S h.mem_Q))
        = rhoLin S (ℓ * x) (aVec S h.mem_Q) := by rw [rhoLin_mul]; rfl
      _ = rhoLin S (x * (x⁻¹ * ℓ * x)) (aVec S h.mem_Q) := by congr 2; group
      _ = rhoLin S x (rhoLin S (x⁻¹ * ℓ * x) (aVec S h.mem_Q)) := by rw [rhoLin_mul]; rfl
      _ = rhoLin S x (aVec S h.mem_Q) := by rw [hLã _ hℓ']
  have hq : qS S (rhoLin S x (aVec S h.mem_Q)) = 0 := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (rhoBar S x).2]
    exact qS_aVec_eq_zero S h.mem_Q h.isConj
  rcases Sec3Hyp.eq_zero_or_eq_aVec_of_fix h hT hfix hq with h0 | h1
  · exfalso
    exact aV_ne_zero S h.mem_Q h.not_mem_ZQ ((rhoLin S x).map_eq_zero_iff.mp h0)
  · exact h1

private theorem eq_one_of_mul_self_eq_one_of_odd {K : Type*} [Group K]
    (hodd : Odd (Nat.card K)) {c : K} (h : c * c = 1) : c = 1 := by
  have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h3 : orderOf c ∣ Nat.card K := orderOf_dvd_natCard c
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hodd.of_dvd_nat h3).coprime_two_right h2)

theorem false_of_symThree_of_orderOf_eq_five (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (hV6 : finrank (ZMod 2) (Additive (QbarOf S)) = 6)
    (hC : Nonempty (Subgroup.centralizer (Xsub S a : Set (Hbar z)) ≃* Perm (Fin 3)))
    {f : Hbar z} (hfX : f ∈ Xsub S a) (hf5 : orderOf f = 5) : False := by
  obtain ⟨ρ, hρC, hρ3, ⟨i, hiC, hi2, hiρ⟩, hclass⟩ :=
    exists_order_three_involution_centralizer_of_isSymThree S hC
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

attribute [local instance] Xsub_normal

theorem false_of_w_eq_three_s6 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1)
    (Ψ : ↥(Xsub S a) ≃* Perm (Fin 6))
    (hΨ : ∀ x : ↥(Xsub S a), (x : Hbar z) ∈ Eset S a ↔ (Ψ x).IsSwap)
    (hΨα : Ψ (alphaInX S h hα₀) = swap 0 1)
    (hZ : ∀ x ∈ commutator ↥(Xsub S a), rhoZ S (x : Hbar z) = 1) (hw : w = 3) : False := by
  classical
  have hR2 : Nat.card ↥(Rbar S a) = 2 := card_Rbar_eq_two S h h217 h3
  have hV6 : finrank (ZMod 2) (Additive (QbarOf S)) = 6 := by
    rw [finrank_QbarOf_eq_two_mul S h.card_F, hw]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_Hbar_prod_s6 S Ψ hΨ
  by_cases hCeven : Even (Nat.card ↥(Subgroup.centralizer (Xsub S a : Set (Hbar z))))
  · obtain ⟨eC⟩ := nonempty_mulEquiv_perm_three_centralizer_Xsub S h h217 hCeven
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    haveI : Fintype ↥(Xsub S a) := Fintype.ofFinite _
    have h5 : 5 ∣ Fintype.card ↥(Xsub S a) := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr Ψ.toEquiv, Nat.card_perm,
        Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
      decide
    obtain ⟨f, hf5⟩ := exists_prime_orderOf_dvd_card (G := ↥(Xsub S a)) 5 h5
    exact false_of_symThree_of_orderOf_eq_five S h h217 hV6 ⟨eC⟩ f.2
      (by rw [Subgroup.orderOf_coe]; exact hf5)
  · have hCodd : Odd (Nat.card ↥(Subgroup.centralizer (Xsub S a : Set (Hbar z)))) :=
      Nat.not_even_iff_odd.mp hCeven
    have hLX : Lbar S a ≤ Xsub S a := by
      intro l hl
      have hl_eq : l = ((ψ l).1 : Hbar z) * ((ψ l).2 : Hbar z) := by
        have h1 := hψ (ψ l)
        rwa [MulEquiv.symm_apply_apply] at h1
      have hl2 : l * l = 1 := by
        have h1 := sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj hl
        rwa [pow_two] at h1
      have hc2 : (ψ l).2 * (ψ l).2 = 1 := by
        have h1 : ψ l * ψ l = 1 := by rw [← map_mul, hl2, map_one]
        have h2 := congrArg Prod.snd h1
        simpa using h2
      have hc1 : (ψ l).2 = 1 := eq_one_of_mul_self_eq_one_of_odd hCodd hc2
      rw [hl_eq, hc1, Subgroup.coe_one, mul_one]
      exact ((ψ l).1).2
    let d : ↥(Xsub S a) := alphaInX S h hα₀
    let LX : Subgroup ↥(Xsub S a) := (Lbar S a).subgroupOf (Xsub S a)
    let Lp : Subgroup (Perm (Fin 6)) := LX.map Ψ.toMonoidHom
    have hLXcard : Nat.card LX = Nat.card (Lbar S a) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv
    have hLpcard : Nat.card Lp = Nat.card LX := Subgroup.card_map_of_injective Ψ.injective
    have hα₀L : α₀ ∈ Lbar S a := Rbar_le_Lbar S a hα₀
    have hd : d ∈ LX := Subgroup.mem_subgroupOf.mpr hα₀L
    have hs : swap 0 1 ∈ Lp := ⟨d, hd, hΨα⟩
    have hsq : ∀ x ∈ Lp, x * x = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul]
      have h1 := sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj (Subgroup.mem_subgroupOf.mp hy)
      have h2 : y * y = 1 := Subtype.ext (by simpa [pow_two] using h1)
      rw [h2, map_one]
    have hcomm : ∀ x ∈ Lp, ∀ y ∈ Lp, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg Ψ (Subtype.ext (commute_of_mem_Lbar S h.mem_Q h.isConj
        (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)))
    have h8 : 8 ≤ Nat.card Lp := by
      rw [hLpcard, hLXcard]
      calc 8 = 2 ^ 3 := by norm_num
        _ = 2 ^ w := by rw [hw]
        _ ≤ _ := h.two_pow_le_card_Lbar
    obtain ⟨g, hgA, hg3, hgN, hg⟩ := exists_threeElement_of_elemAbelian Lp hs hsq hcomm h8
    obtain ⟨γ', hγ'def⟩ : ∃ γ' : ↥(Xsub S a), γ' = Ψ.symm g := ⟨_, rfl⟩
    obtain ⟨γ, hγdef⟩ : ∃ γ : Hbar z, γ = (γ' : Hbar z) := ⟨_, rfl⟩
    have hΨγ : Ψ γ' = g := by rw [hγ'def]; exact Ψ.apply_symm_apply g
    have hγ3 : γ ^ 3 = 1 := by
      have h1 : γ' ^ 3 = 1 := Ψ.injective (by rw [map_pow, hΨγ, hg3, map_one])
      rw [hγdef]
      simpa using congrArg Subtype.val h1
    have hγ_odd : Odd (orderOf γ) :=
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hγ3)
    have hγX' : γ' ∈ commutator ↥(Xsub S a) := by
      have h1 : g ∈ commutator (Perm (Fin 6)) := by
        rw [alternatingGroup.commutator_perm_eq (by simp)]
        exact hgA
      rw [← TauCeti.Subgroup.map_commutator_eq_commutator (f := Ψ.toMonoidHom) Ψ.surjective]
        at h1
      obtain ⟨x, hx, hxg⟩ := h1
      have h2 : x = γ' := Ψ.injective (by rw [hΨγ]; exact hxg)
      exact h2 ▸ hx
    have hconj1 : ∀ ℓ ∈ Lbar S a, γ * ℓ * γ⁻¹ ∈ Lbar S a := by
      intro ℓ hℓ
      rw [hγdef]
      have hℓX : ℓ ∈ Xsub S a := hLX hℓ
      have hmem : Ψ ⟨ℓ, hℓX⟩ ∈ Lp := ⟨⟨ℓ, hℓX⟩, Subgroup.mem_subgroupOf.mpr hℓ, rfl⟩
      obtain ⟨y, hy, hyΨ⟩ := hgN _ hmem
      have hy_eq : y = γ' * ⟨ℓ, hℓX⟩ * γ'⁻¹ :=
        Ψ.injective (by
          have h1 : Ψ y = g * Ψ ⟨ℓ, hℓX⟩ * g⁻¹ := hyΨ
          rw [h1, map_mul, map_mul, map_inv, hΨγ])
      have h2 := Subgroup.mem_subgroupOf.mp hy
      rw [hy_eq] at h2
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h2
    have hγinv : γ⁻¹ = γ * γ := by
      refine inv_eq_of_mul_eq_one_right ?_
      calc γ * (γ * γ) = γ ^ 3 := (pow_three γ).symm
        _ = 1 := hγ3
    have hconj2 : ∀ ℓ ∈ Lbar S a, γ⁻¹ * ℓ * γ ∈ Lbar S a := by
      intro ℓ hℓ
      have h1 := hconj1 _ (hconj1 ℓ hℓ)
      have h2 : γ⁻¹ * ℓ * γ = γ * (γ * ℓ * γ⁻¹) * γ⁻¹ := by
        calc γ⁻¹ * ℓ * γ = (γ * γ) * ℓ * (γ * γ)⁻¹ := by rw [← hγinv, inv_inv]
          _ = γ * (γ * ℓ * γ⁻¹) * γ⁻¹ := by group
      rw [h2]
      exact h1
    have hγN : γ ∈ Subgroup.normalizer (Lbar S a : Set (Hbar z)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro ℓ
      refine ⟨fun hℓ => hconj1 ℓ hℓ, fun hℓ => ?_⟩
      have h1 := hconj2 _ hℓ
      simpa [mul_assoc] using h1
    have haγ : rhoLin S γ (aVec S h.mem_Q) = aVec S h.mem_Q :=
      rhoLin_aVec_eq_of_mem_normalizer_Lbar S h h217 h3 hγN
    let Hfix : Subgroup (Hbar z) :=
      (MulAction.stabilizer (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))
        (aVec S h.mem_Q)).comap (rhoGL S)
    have hmemHfix : ∀ y, y ∈ Hfix ↔ rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q := fun y => by
      simp [Hfix, MulAction.mem_stabilizer_iff, rhoGL_apply, LinearEquiv.smul_def]
    let Y : Subgroup (Hbar z) := Hfix ⊓ (rhoZ S).ker
    have hγY : γ ∈ Y :=
      ⟨(hmemHfix γ).mpr haγ, MonoidHom.mem_ker.mpr (by rw [hγdef]; exact hZ γ' hγX')⟩
    have hγCH : γ ∈ CHbar S a :=
      mem_CHbar_of_odd_orderOf S h.mem_Q (Y := Y) (fun y hy => (hmemHfix y).mp hy.1)
        (fun y hy u => by rw [MonoidHom.mem_ker.mp hy.2]; rfl) hγY hγ_odd
    have hγα : γ * α₀ = α₀ * γ :=
      commute_of_mem_CHbar_of_card_Rbar_eq_two S a hR2 hα₀ hα₀1 hγCH
    have hgs : g * swap 0 1 = swap 0 1 * g := by
      have h1 : γ' * d = d * γ' := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hγdef]; exact hγα)
      have h2 := congrArg Ψ h1
      rwa [map_mul, map_mul, hΨγ, hΨα] at h2
    rcases hg with hg1 | ⟨-, hK⟩
    · exact hg1 hgs
    · have hα₀T : α₀ ∈ Tset S a := h.mem_Tset_of_mem_Rbar hα₀ hα₀1
      have hT : ∀ α ∈ Tset S a, ∀ β ∈ Tset S a, α * β ∉ Tset S a :=
        fun α hα β hβ => stroth78_35 S h h217 h3 hα hβ
      have hP_tr : ∀ v ∈ commSpace (rhoLin S α₀), rhoLin S γ v = v :=
        rhoLin_apply_eq_self_of_odd_of_commute S h hα₀ hγα hγ_odd haγ
      have hP_trinv : ∀ u ∈ commSpace (rhoLin S α₀), rhoLin S γ⁻¹ u = u := by
        intro u hu
        rw [rhoLin_inv]
        exact (LinearEquiv.symm_apply_eq _).mpr (hP_tr u hu).symm
      let K₀ : Subgroup (Hbar z) :=
        (fixingSubgroup (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))
          (commSpace (rhoLin S α₀) : Set (Additive (QbarOf S)))).comap (rhoGL S)
      have hmemK₀ : ∀ y, y ∈ K₀ ↔ ∀ v ∈ commSpace (rhoLin S α₀), rhoLin S y v = v :=
        fun y => by
          simp [K₀, mem_fixingSubgroup_iff, rhoGL_apply, LinearEquiv.smul_def]
      let K : Subgroup (Perm (Fin 6)) :=
        ((Lbar S a ⊓ K₀).subgroupOf (Xsub S a)).map Ψ.toMonoidHom
      have hKLp : K ≤ Lp := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hy).1, rfl⟩
      have hrho1 : rhoLin S (1 : Hbar z) = 1 := by simp [rhoLin]
      have hα₀K₀ : α₀ ∈ K₀ := by
        rw [hmemK₀]
        intro v hv
        have hf : rhoLin S α₀ * rhoLin S α₀ = 1 := by
          rw [← rhoLin_mul, ← pow_two, sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj hα₀L, hrho1]
        exact CFSG.LargeExtraspecial.DW.W4.mem_fixSpace.mp
          (CFSG.LargeExtraspecial.DW.W4.commSpace_le_fixSpace hf hv)
      have hsK : swap 0 1 ∈ K := ⟨d, Subgroup.mem_subgroupOf.mpr ⟨hα₀L, hα₀K₀⟩, hΨα⟩
      have hKc : ∀ ℓ ∈ Lp, g * ℓ * g⁻¹ * ℓ⁻¹ ∈ K := by
        rintro _ ⟨y, hy, rfl⟩
        have hyL : (y : Hbar z) ∈ Lbar S a := Subgroup.mem_subgroupOf.mp hy
        have hcoe : ((γ' * y * γ'⁻¹ * y⁻¹ : ↥(Xsub S a)) : Hbar z) =
            γ * (y : Hbar z) * γ⁻¹ * (y : Hbar z)⁻¹ := by
          rw [hγdef]
          simp [Subgroup.coe_mul, Subgroup.coe_inv]
        refine ⟨γ' * y * γ'⁻¹ * y⁻¹,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩), ?_⟩
        · rw [hcoe]
          exact (Lbar S a).mul_mem (hconj1 _ hyL) ((Lbar S a).inv_mem hyL)
        · rw [hcoe, hmemK₀]
          intro v hv
          have hv1 : rhoLin S (y : Hbar z)⁻¹ v ∈ commSpace (rhoLin S α₀) :=
            rhoLin_mem_commSpace_of_commute S
              (commute_of_mem_Lbar S h.mem_Q h.isConj ((Lbar S a).inv_mem hyL) hα₀L) hv
          have e1 : rhoLin S (γ * (y : Hbar z) * γ⁻¹ * (y : Hbar z)⁻¹) v =
              rhoLin S γ (rhoLin S (y : Hbar z) (rhoLin S γ⁻¹ (rhoLin S (y : Hbar z)⁻¹ v))) := by
            rw [rhoLin_mul, rhoLin_mul, rhoLin_mul]
            rfl
          have e2 : rhoLin S (y : Hbar z) (rhoLin S (y : Hbar z)⁻¹ v) = v := by
            have : rhoLin S ((y : Hbar z) * (y : Hbar z)⁻¹) v = v := by
              rw [mul_inv_cancel, hrho1]; rfl
            rw [rhoLin_mul] at this
            exact this
          rw [e1, hP_trinv _ hv1, e2]
          exact hP_tr v hv
        · simp [map_mul, map_inv, hΨγ]
      have hKeq := hK K hKLp hsK hKc
      have hall : ∀ ℓ ∈ Lbar S a, ∀ v ∈ commSpace (rhoLin S α₀), rhoLin S ℓ v = v := by
        intro ℓ hℓ
        have hℓX : ℓ ∈ Xsub S a := hLX hℓ
        have hmem : Ψ ⟨ℓ, hℓX⟩ ∈ K := by
          rw [hKeq]
          exact ⟨⟨ℓ, hℓX⟩, Subgroup.mem_subgroupOf.mpr hℓ, rfl⟩
        obtain ⟨y, hy, hyΨ⟩ := hmem
        have hyeq : y = ⟨ℓ, hℓX⟩ := Ψ.injective hyΨ
        have h1 := (Subgroup.mem_subgroupOf.mp hy).2
        rw [hyeq] at h1
        exact (hmemK₀ ℓ).mp h1
      exact Sec3Hyp.not_forall_Lbar_fix_commSpace h hT hα₀T.2.2 hall

end CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6
