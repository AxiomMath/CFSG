module

public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeAct
public import CFSG.RankThree.GF2n.Stroth78.Sec3Three

import CFSG.Fischer.Classification.Symmetric.Inner
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Perm
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6Quot

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions Equiv Equiv.Perm

private theorem exists_mulEquiv_prod_centralizer_of_conj {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (hZ : Subgroup.center N = ⊥)
    (hinner : ∀ g : G, ∃ n : N, MulAut.conjNormal g = MulAut.conj n) :
    ∃ ψ : G ≃* N × Subgroup.centralizer (N : Set G), ∀ p, ψ.symm p = (p.1 : G) * p.2 := by
  set C := Subgroup.centralizer (N : Set G) with hC
  have hcomm : ∀ (n : N) (c : C), Commute (N.subtype n) (C.subtype c) := fun n c =>
    (Subgroup.mem_centralizer_iff.mp c.2 n n.2)
  let f : N × C →* G := MonoidHom.noncommCoprod N.subtype C.subtype hcomm
  have hf : ∀ p : N × C, f p = (p.1 : G) * p.2 := fun _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_one]
      rintro ⟨n, c⟩ h1
      rw [hf] at h1
      have hnc : (n : G) = (c : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hn : n ∈ Subgroup.center N := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        change (y : G) * n = n * y
        have hyc : (y : G) * c = c * y := Subgroup.mem_centralizer_iff.mp c.2 y y.2
        rw [hnc]
        calc (y : G) * (c : G)⁻¹ = (c : G)⁻¹ * ((c : G) * y) * (c : G)⁻¹ := by group
          _ = (c : G)⁻¹ * ((y : G) * c) * (c : G)⁻¹ := by rw [hyc]
          _ = (c : G)⁻¹ * y := by group
      rw [hZ, Subgroup.mem_bot] at hn
      have hc : c = 1 := by
        apply Subtype.ext
        have : (c : G)⁻¹ = 1 := by rw [← hnc, hn]; rfl
        rw [inv_eq_one] at this
        exact this
      rw [hn, hc]
      rfl
    · intro g
      obtain ⟨n, hn⟩ := hinner g
      have hgc : (n : G)⁻¹ * g ∈ C := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 := congrArg (fun φ : MulAut N => ((φ ⟨x, hx⟩ : N) : G)) hn
        simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] at h1
        calc x * ((n : G)⁻¹ * g) = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * g := by group
          _ = (n : G)⁻¹ * (g * x * g⁻¹) * g := by rw [← h1]
          _ = (n : G)⁻¹ * g * x := by group
      refine ⟨(n, ⟨(n : G)⁻¹ * g, hgc⟩), ?_⟩
      rw [hf]
      change (n : G) * ((n : G)⁻¹ * g) = g
      group
  exact ⟨(MulEquiv.ofBijective f hbij).symm, fun p => rfl⟩

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

theorem exists_mulEquiv_Hbar_prod_s6 (S : Setting z E F) {a : G}
    (Ψ : ↥(Xsub S a) ≃* Perm (Fin 6))
    (hΨ : ∀ x : ↥(Xsub S a), (x : Hbar z) ∈ Eset S a ↔ (Ψ x).IsSwap) :
    ∃ ψ : Hbar z ≃* ↥(Xsub S a) × ↥(Subgroup.centralizer (Xsub S a : Set (Hbar z))),
      ∀ p, ψ.symm p = (p.1 : Hbar z) * p.2 := by
  have hZ : Subgroup.center ↥(Xsub S a) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    refine Ψ.injective ?_
    rw [map_one]
    refine CFSG.perm_eq_one_of_forall_commute (by simp) fun y => ?_
    obtain ⟨y', rfl⟩ := Ψ.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y']
  have hinner : ∀ g : Hbar z, ∃ n : ↥(Xsub S a), MulAut.conjNormal g = MulAut.conj n := by
    intro g
    refine CFSG.Fischer.Classification.SymPair.exists_eq_conj_of_mulEquiv_perm
      (D := (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a))) (by norm_num) Ψ hΨ
      (MulAut.conjNormal g) fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have h1 := Eset_conj_mem S a (hx : (x : Hbar z) ∈ Eset S a) g
      show ((MulAut.conjNormal g x : ↥(Xsub S a)) : Hbar z) ∈ Eset S a
      rw [MulAut.conjNormal_apply]
      exact h1
    · have h1 := Eset_conj_mem S a
        (hx : ((MulAut.conjNormal g x : ↥(Xsub S a)) : Hbar z) ∈ Eset S a) g⁻¹
      rw [MulAut.conjNormal_apply] at h1
      have h2 : g⁻¹ * (g * (x : Hbar z) * g⁻¹) * g⁻¹⁻¹ = (x : Hbar z) := by group
      rw [h2] at h1
      exact h1
  exact exists_mulEquiv_prod_centralizer_of_conj (Xsub S a) hZ hinner

theorem card_inf_centralizer_le_two (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) ≤ 2 := by
  have hK2 : IsPGroup 2 ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) :=
    (isElemAbelian_Lbar S h.mem_Q h.isConj).isPGroup.to_le inf_le_left
  obtain ⟨n, hn⟩ := hK2.exists_card_eq
  have hdvd : 2 ^ n ∣ 6 := by
    rw [← hn]
    exact (Subgroup.card_dvd_of_le inf_le_right).trans (card_centralizer_Xsub_dvd_six S h h217)
  have hnle : n ≤ 1 := by
    by_contra hn2
    push Not at hn2
    have h4 : 2 ^ 2 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
    have h5 := h4.trans hdvd
    norm_num at h5
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hnle
    _ = 2 := by norm_num

theorem card_Lbar_eq_mul_card_map (S : Setting z E F) {a : G}
    (ψ : Hbar z ≃* ↥(Xsub S a) × ↥(Subgroup.centralizer (Xsub S a : Set (Hbar z))))
    (hψ : ∀ p, ψ.symm p = (p.1 : Hbar z) * p.2) :
    ∃ k : ℕ, Nat.card (Lbar S a) =
        k * Nat.card ↥((Lbar S a).map ((MonoidHom.fst _ _).comp ψ.toMonoidHom)) ∧
      k ≤ Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) := by
  let π₁ : Hbar z →* ↥(Xsub S a) := (MonoidHom.fst _ _).comp ψ.toMonoidHom
  let g : ↥(Lbar S a) →* ↥(Xsub S a) := π₁.comp (Lbar S a).subtype
  have hrange : g.range = (Lbar S a).map π₁ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨Nat.card g.ker, ?_, ?_⟩
  · rw [← hrange, ← Subgroup.card_ker_mul_card_range g]
  · let f : ↥g.ker → ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) := fun x =>
      ⟨((x.1 : ↥(Lbar S a)) : Hbar z), x.1.2, by
        have h1 : π₁ ((x.1 : ↥(Lbar S a)) : Hbar z) = 1 := MonoidHom.mem_ker.mp x.2
        have h2 := hψ (ψ ((x.1 : ↥(Lbar S a)) : Hbar z))
        rw [MulEquiv.symm_apply_apply] at h2
        have h3 : (ψ ((x.1 : ↥(Lbar S a)) : Hbar z)).1 = 1 := h1
        rw [h3] at h2
        rw [h2]
        simpa using (ψ ((x.1 : ↥(Lbar S a)) : Hbar z)).2.2⟩
    refine Nat.card_le_card_of_injective f fun x y hxy => ?_
    have := congrArg (fun t : ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) =>
      (t : Hbar z)) hxy
    exact Subtype.ext (Subtype.ext this)

theorem card_map_Lbar_le_eight (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (Ψ : ↥(Xsub S a) ≃* Perm (Fin 6))
    (π₁ : Hbar z →* ↥(Xsub S a)) :
    Nat.card ↥((Lbar S a).map π₁) ≤ 8 := by
  have hmap := card_le_eight_of_elemAbelian ((Lbar S a).map (Ψ.toMonoidHom.comp π₁))
    (fun x hx => by
      obtain ⟨ℓ, hℓ, rfl⟩ := hx
      rw [← map_mul]
      have h1 := sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj hℓ
      rw [pow_two] at h1
      rw [h1, map_one])
    (fun x hx y hy => by
      obtain ⟨ℓ, hℓ, rfl⟩ := hx
      obtain ⟨ℓ', hℓ', rfl⟩ := hy
      rw [← map_mul, ← map_mul, commute_of_mem_Lbar S h.mem_Q h.isConj hℓ hℓ'])
  rw [← Subgroup.map_map, Subgroup.card_map_of_injective Ψ.injective] at hmap
  exact hmap

theorem card_Lbar_le_sixteen (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (Ψ : ↥(Xsub S a) ≃* Perm (Fin 6))
    (hΨ : ∀ x : ↥(Xsub S a), (x : Hbar z) ∈ Eset S a ↔ (Ψ x).IsSwap) :
    Nat.card (Lbar S a) ≤ 16 := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_Hbar_prod_s6 S Ψ hΨ
  obtain ⟨k, hk, hkle⟩ := card_Lbar_eq_mul_card_map S ψ hψ
  have h2 := card_inf_centralizer_le_two S h h217
  have hr := card_map_Lbar_le_eight S h Ψ ((MonoidHom.fst _ _).comp ψ.toMonoidHom)
  rw [hk]
  exact (Nat.mul_le_mul (hkle.trans h2) hr).trans (by norm_num)

theorem nonempty_mulEquiv_Hbar_perm_six_prod_perm_three (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (Ψ : ↥(Xsub S a) ≃* Perm (Fin 6))
    (hΨ : ∀ x : ↥(Xsub S a), (x : Hbar z) ∈ Eset S a ↔ (Ψ x).IsSwap) (hw : 4 ≤ w) :
    Nonempty (Hbar z ≃* Perm (Fin 6) × Perm (Fin 3)) := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_Hbar_prod_s6 S Ψ hΨ
  obtain ⟨k, hk, hkle⟩ := card_Lbar_eq_mul_card_map S ψ hψ
  have hr := card_map_Lbar_le_eight S h Ψ ((MonoidHom.fst _ _).comp ψ.toMonoidHom)
  have hL : 16 ≤ Nat.card (Lbar S a) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
      _ ≤ _ := h.two_pow_le_card_Lbar
  have hk2 : 2 ≤ k := by
    by_contra hk1
    push Not at hk1
    have h1 : k * Nat.card ↥((Lbar S a).map ((MonoidHom.fst _ _).comp ψ.toMonoidHom)) ≤ 1 * 8 :=
      Nat.mul_le_mul (by omega) hr
    omega
  have hK : 2 ≤ Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) :=
    hk2.trans hkle
  have hK2 : IsPGroup 2 ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) :=
    (isElemAbelian_Lbar S h.mem_Q h.isConj).isPGroup.to_le inf_le_left
  obtain ⟨n, hn⟩ := hK2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have h2dvd : 2 ∣ Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  have heven : Even (Nat.card (Subgroup.centralizer (Xsub S a : Set (Hbar z)))) :=
    even_iff_two_dvd.mpr (h2dvd.trans (Subgroup.card_dvd_of_le inf_le_right))
  obtain ⟨eC⟩ := nonempty_mulEquiv_perm_three_centralizer_Xsub S h h217 heven
  exact ⟨ψ.trans (MulEquiv.prodCongr Ψ eC)⟩

theorem exists_mulEquiv_Xsub_perm_six_swap (S : Setting z E F) {a : G} {w : ℕ}
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
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1)
    (φ : ↥(threeResidualQuot (alphaInX S h hα₀)) ≃* Perm (Fin 6))
    (hφ : ∀ g, g ∈ threeResidualClass (alphaInX S h hα₀) ↔ (φ g).IsSwap) :
    ∃ Ψ : ↥(Xsub S a) ≃* Perm (Fin 6),
      (∀ x : ↥(Xsub S a), (x : Hbar z) ∈ Eset S a ↔ (Ψ x).IsSwap) ∧
        Ψ (alphaInX S h hα₀) = swap 0 1 := by
  obtain ⟨Ψ₁, hΨ₁⟩ := exists_mulEquiv_Xsub_perm_six S h h217 h3 hα₀ hα₀1 φ hφ
  have hd : (Ψ₁ (alphaInX S h hα₀)).IsSwap :=
    (hΨ₁ _).mp (Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀ hα₀1))
  obtain ⟨u, v, huv, hduv⟩ := hd
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_swap huv (by decide : (0 : Fin 6) ≠ 1) :
      IsConj (swap u v) (swap (0 : Fin 6) 1))
  have hconj : ∀ y : Perm (Fin 6), (c * y * c⁻¹).IsSwap ↔ y.IsSwap := fun y => by
    rw [← Equiv.Perm.card_support_eq_two, ← Equiv.Perm.card_support_eq_two,
      Equiv.Perm.card_support_conj]
  refine ⟨Ψ₁.trans (MulAut.conj c), fun x => (hΨ₁ x).trans (hconj _).symm, ?_⟩
  show c * Ψ₁ (alphaInX S h hα₀) * c⁻¹ = swap 0 1
  rw [hduv, hc]

end CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6
