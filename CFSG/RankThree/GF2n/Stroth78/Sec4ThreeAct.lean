module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidualConj
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp

import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.GroupTheory.ThreeTranspositions.FischerResidualAction

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.GroupTheory.ThreeTranspositions

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

local instance instNormalXsub (S : Setting z E F) (a : G) : (Xsub S a).Normal :=
  Xsub_normal S a

@[expose] noncomputable def alphaInX (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) : ↥(Xsub S a) :=
  ⟨α, h.Rbar_le_Xsub hα⟩

@[simp] theorem coe_alphaInX (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) : ((alphaInX S h hα : ↥(Xsub S a)) : Hbar z) = α :=
  rfl

theorem Lbar_le_centralizer (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) :
    Lbar S a ≤ Subgroup.centralizer ({α} : Set (Hbar z)) := by
  intro ℓ hℓ
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (commute_of_mem_Lbar S h.mem_Q h.isConj hℓ (Rbar_le_Lbar S a hα)).symm

noncomputable def actL (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) :
    ↥(Lbar S a) →* MulAut ↥(threeResidualQuot (alphaInX S h hα)) :=
  (residualConj (alphaInX S h hα)).comp
    (Subgroup.inclusion (Lbar_le_centralizer S h hα))

theorem actL_apply (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) (ℓ : ↥(Lbar S a)) (n : ↥(Xsub S a))
    (hn : (QuotientGroup.mk n :
        ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) ∈
      threeResidualQuot (alphaInX S h hα)) :
    ((actL S h hα ℓ) ⟨QuotientGroup.mk n, hn⟩ :
        ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) =
      QuotientGroup.mk (MulAut.conjNormal (ℓ : Hbar z) n) := by
  exact residualConj_apply_mk (d := alphaInX S h hα)
    (Subgroup.inclusion (Lbar_le_centralizer S h hα) ℓ) n hn

theorem isPGroup_range_actL (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) :
    IsPGroup 2 (actL S h hα).range := by
  obtain ⟨n, hn⟩ := (isElemAbelian_Lbar S h.mem_Q h.isConj).isPGroup.exists_card_eq
  have hdvd : Nat.card ↥(actL S h hα).range ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.card_range_dvd _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact IsPGroup.of_card hk

theorem actL_fix (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) (ℓ : ↥(Lbar S a)) :
    actL S h hα ℓ ⟨QuotientGroup.mk (alphaInX S h hα),
        mk_mem_threeResidualQuot_self (alphaInX S h hα)⟩ =
      ⟨QuotientGroup.mk (alphaInX S h hα),
        mk_mem_threeResidualQuot_self (alphaInX S h hα)⟩ := by
  exact residualConj_fix_self (d := alphaInX S h hα)
    (c := Subgroup.inclusion (Lbar_le_centralizer S h hα) ℓ)

theorem actL_mem_threeResidualClass (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {α : Hbar z} (hα : α ∈ Rbar S a) (ℓ : ↥(Lbar S a))
    {x : ↥(threeResidualQuot (alphaInX S h hα))}
    (hx : x ∈ threeResidualClass (alphaInX S h hα)) :
    actL S h hα ℓ x ∈ threeResidualClass (alphaInX S h hα) := by
  exact residualConj_mem_threeResidualClass
    (c := Subgroup.inclusion (Lbar_le_centralizer S h hα) ℓ) hx

theorem mem_centralizer_of_actL_eq_one (S : Setting z E F) {a : G} {w : ℕ}
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
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1)
    {ℓ : ↥(Lbar S a)} (hℓ : actL S h hα ℓ = 1) :
    (ℓ : Hbar z) ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) := by
  have hαT : α ∈ Tset S a := h.mem_Tset_of_mem_Rbar hα hα1
  have hαE : α ∈ Eset S a := Tset_subset_Eset S a hαT
  obtain ⟨N₀, hN₀n, hN₀c, hN₀le⟩ :=
    exists_normal_le_threeResidualQuot (X := ↥(Xsub S a))
      (E := Subtype.val ⁻¹' Eset S a) (pair_Xsub S h h217 h3)
      (twoCore_Xsub S) (threeCore_Xsub S h h217) (d := alphaInX S h hα) hαE
  have hℓ' : residualConj (alphaInX S h hα)
      (Subgroup.inclusion (Lbar_le_centralizer S h hα) ℓ) = 1 := hℓ
  have hg : ∀ n : ↥(Xsub S a),
      (QuotientGroup.mk n : ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) ∈ N₀ →
      (MulAut.conjNormal (H := Xsub S a) (ℓ : Hbar z)) n / n ∈
        Subgroup.center ↥(Xsub S a) := by
    intro n hn
    exact conjNormal_div_mem_center_of_residualConj_eq_one hℓ' n (hN₀le hn)
  exact mem_centralizer_of_trivial_on_normal (N := Xsub S a) (K := N₀)
    (g := (ℓ : Hbar z)) (closure_involutions_Xsub S a) (odd_card_center_Xsub S a)
    hN₀n hN₀c hg

theorem card_inf_centralizer_Xsub_le_two (S : Setting z E F) {a : G} {w : ℕ}
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
  let K : Subgroup (Hbar z) :=
    Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))
  have hK2 : IsPGroup 2 K :=
    (isElemAbelian_Lbar S h.mem_Q h.isConj).isPGroup.to_le inf_le_left
  obtain ⟨n, hn⟩ := hK2.exists_card_eq
  have hdvd : Nat.card K ∣ 6 :=
    (Subgroup.card_dvd_of_le inf_le_right).trans (card_centralizer_Xsub_dvd_six S h h217)
  have hn1 : n ≤ 1 := by
    by_contra hn1
    push Not at hn1
    have h4dvd : 4 ∣ 2 ^ n := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
      rw [hk, pow_add]
      norm_num
    rw [hn] at hdvd
    have h46 : 4 ∣ 6 := h4dvd.trans hdvd
    norm_num at h46
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) hn1

theorem card_Lbar_le_two_mul_card_range_actL (S : Setting z E F) {a : G} {w : ℕ}
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
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1) :
    Nat.card (Lbar S a) ≤ 2 * Nat.card (actL S h hα).range := by
  have hker : Nat.card ↥(actL S h hα).ker ≤ 2 := by
    let K : Subgroup (Hbar z) :=
      Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))
    let f : ↥(actL S h hα).ker → ↥K := fun k =>
      ⟨(k.1 : Hbar z), by
        refine Subgroup.mem_inf.mpr ⟨k.1.2, ?_⟩
        exact mem_centralizer_of_actL_eq_one S h h217 h3 hα hα1
          (MonoidHom.mem_ker.mp k.2)⟩
    have hf : Function.Injective f := by
      intro k k' hkk'
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : ↥K => (t : Hbar z)) hkk'
    calc
      Nat.card ↥(actL S h hα).ker ≤ Nat.card ↥K :=
        Nat.card_le_card_of_injective f hf
      _ ≤ 2 := card_inf_centralizer_Xsub_le_two S h h217
  calc
    Nat.card (Lbar S a) =
        Nat.card ↥(actL S h hα).ker * Nat.card (actL S h hα).range :=
      (Subgroup.card_ker_mul_card_range (actL S h hα)).symm
    _ ≤ 2 * Nat.card (actL S h hα).range := Nat.mul_le_mul_right _ hker

end CFSG.RankThree.GF2n.Stroth78
