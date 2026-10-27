module

public import CFSG.GroupTheory.OddInversion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] def W172Inv (d : Γ) (Y : Subgroup Γ) : Set Γ :=
  {y | y ∈ Y ∧ d * y * d⁻¹ = y⁻¹}

structure W172InvSetup (p : ℕ) (X : Subgroup Γ) (d : Γ) (S : Subgroup Γ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  pgroup : IsPGroup p X
  sq : d ^ 2 = 1
  d_norm : ∀ x ∈ X, d * x * d⁻¹ ∈ X
  s_norm : ∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ ∈ X
  s_comm : ∀ s ∈ S, s * d = d * s

structure W172MinInv (p : ℕ) (X : Subgroup Γ) (d : Γ) (S Y : Subgroup Γ) : Prop
    extends W172InvSetup p X d S where
  le : Y ≤ X
  d_mem : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y
  s_mem : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y
  nontriv : ∃ y ∈ Y, d * y * d⁻¹ ≠ y
  minimal : ∀ Z : Subgroup Γ, Z ≤ Y → (∀ z ∈ Z, d * z * d⁻¹ ∈ Z) →
    (∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ ∈ Z) → (∃ z ∈ Z, d * z * d⁻¹ ≠ z) → Z = Y

private theorem w172_mul_self_eq_one_of_sq_eq_one {d : Γ} (h : d ^ 2 = 1) : d * d = 1 := by
  simpa [pow_two] using h

private theorem w172_inv_eq_self_of_sq_eq_one {d : Γ} (h : d ^ 2 = 1) : d⁻¹ = d :=
  inv_eq_of_mul_eq_one_right (w172_mul_self_eq_one_of_sq_eq_one h)

private theorem w172_conj_conj_eq_self {d y : Γ} (hd : d * d = 1) :
    d * (d * y * d⁻¹) * d⁻¹ = y := by
  have hd_inv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  rw [hd_inv, show d * (d * y * d) * d = (d * d) * y * (d * d) by group, hd, one_mul, mul_one]

private theorem w172_conj_eq_self_of_comm {d s : Γ} (h : s * d = d * s) : d * s * d⁻¹ = s := by
  rw [← h, mul_assoc, mul_inv_cancel, mul_one]

private theorem w172_conj_inv_eq_inv_of_comm {d s : Γ} (h : s * d = d * s) :
    d * s⁻¹ * d⁻¹ = s⁻¹ := by
  have h1 := w172_conj_eq_self_of_comm h
  simpa [mul_assoc] using congrArg Inv.inv h1

private theorem w172_conj_conj_mul {d s y : Γ} (h : s * d = d * s) :
    d * (s * y * s⁻¹) * d⁻¹ = s * (d * y * d⁻¹) * s⁻¹ := by
  rw [show d * (s * y * s⁻¹) * d⁻¹ =
      (d * s * d⁻¹) * (d * y * d⁻¹) * (d * s⁻¹ * d⁻¹) by group,
    w172_conj_eq_self_of_comm h, w172_conj_inv_eq_inv_of_comm h]

private theorem w172_conj_tau {d s y : Γ} (h : s * d = d * s) :
    s * (y⁻¹ * (d * y * d⁻¹)) * s⁻¹ =
      (s * y * s⁻¹)⁻¹ * (d * (s * y * s⁻¹) * d⁻¹) := by
  rw [w172_conj_conj_mul h]
  group

private theorem w172_conj_inv_conj_inv_mul {d y : Γ} (hd : d * d = 1) :
    d * (y⁻¹ * (d * y * d⁻¹)) * d⁻¹ = (d * y * d⁻¹)⁻¹ * y := by
  have hd_inv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  rw [hd_inv, show d * (y⁻¹ * (d * y * d)) * d = (d * y⁻¹ * d) * y * (d * d) by group, hd,
    mul_one]
  simp only [mul_inv_rev, hd_inv]
  group

private instance w172_finiteSubgroup (H : Subgroup Γ) : Finite (Subgroup H) :=
  Finite.of_injective (fun K : Subgroup H => (K : Set H)) SetLike.coe_injective

private theorem w172_frattini_lt_top {Y : Subgroup Γ} [Nontrivial ↥Y] : frattini ↥Y < ⊤ := by
  obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (α := Subgroup ↥Y)
  exact lt_of_le_of_lt (frattini_le_coatom hM) hM.1.lt_top

private theorem w172_nontrivial_of_minInv {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) : Nontrivial ↥Y := by
  obtain ⟨y, hy, hne⟩ := h.nontriv
  exact ⟨⟨y, hy⟩, 1, fun hcon => hne (by
    have : y = 1 := Subtype.ext_iff.mp hcon
    rw [this]; simp)⟩

private theorem w172_eq_one_of_mem_of_inverted_of_fixed {Y : Subgroup Γ} (hYodd : Odd (Nat.card Y))
    {d y : Γ} (hy : y ∈ Y) (hinv : d * y * d⁻¹ = y⁻¹) (hfix : d * y * d⁻¹ = y) : y = 1 := by
  have h1 : y = y⁻¹ := hfix.symm.trans hinv
  have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr h1
  have hdvd2 : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
  have hodd : Odd (orderOf y) := hYodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hy)
  have h1' : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1'

private theorem w172_mem_normalizer_of_normalizes {Y : Subgroup Γ} {d : Γ}
    (hd : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) (hd_mul : d * d = 1) :
    d ∈ Subgroup.normalizer (Y : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨hd y, fun hy => by
    have h := hd (d * y * d⁻¹) hy
    rwa [w172_conj_conj_eq_self hd_mul] at h⟩

private theorem w172_minInv_centralizes_of_ne {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) {Z : Subgroup Γ} (hZY : Z ≤ Y)
    (hdZ : ∀ z ∈ Z, d * z * d⁻¹ ∈ Z) (hsZ : ∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ ∈ Z)
    (hne : Z ≠ Y) : ∀ z ∈ Z, d * z * d⁻¹ = z := by
  intro z hz
  by_contra hcon
  exact hne (h.minimal Z hZY hdZ hsZ ⟨z, hz, hcon⟩)

private theorem w172_commutator_lt_self {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) : (⁅Y, Y⁆ : Subgroup Γ) < Y := by
  have hYp : IsPGroup p Y := h.pgroup.to_le h.le
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Nontrivial ↥Y := w172_nontrivial_of_minInv h
  haveI : Group.IsNilpotent ↥Y := IsPGroup.isNilpotent hYp
  haveI : Group.IsSolvable ↥Y := inferInstance
  have hlt : (_root_.commutator ↥Y).map Y.subtype < (⊤ : Subgroup ↥Y).map Y.subtype :=
    (Subgroup.map_subtype_lt_map_subtype (G' := Y) (H := _root_.commutator ↥Y)
      (K := ⊤)).mpr (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥Y))
  have htop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    simpa [MonoidHom.range_eq_map] using (Y.range_subtype : Y.subtype.range = Y)
  simpa [Subgroup.map_subtype_commutator, htop] using hlt

private theorem w172_mem_commutator_of_conj {Y : Subgroup Γ} {a q : Γ} (ha : a ∈ Y)
    (hq : q ∈ (⁅Y, Y⁆ : Subgroup Γ)) : a * q * a⁻¹ ∈ (⁅Y, Y⁆ : Subgroup Γ) :=
  (Subgroup.mem_normalizer_iff.mp
    (Subgroup.normalizer_commutator_ge_left (H₁ := Y) (H₂ := Y) ha) q).mp hq

theorem w172_exists_minInv {p : ℕ} {X : Subgroup Γ} {d : Γ} {S : Subgroup Γ}
    (hset : W172InvSetup p X d S) (hnt : ∃ x ∈ X, d * x * d⁻¹ ≠ x) :
    ∃ Y : Subgroup Γ, W172MinInv p X d S Y := by
  classical
  let 𝒮 : Set (Subgroup Γ) := {Z | Z ≤ X ∧ (∀ z ∈ Z, d * z * d⁻¹ ∈ Z) ∧
    (∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ ∈ Z) ∧ ∃ z ∈ Z, d * z * d⁻¹ ≠ z}
  have hXmem : X ∈ 𝒮 := ⟨le_rfl, hset.d_norm, hset.s_norm, hnt⟩
  have hex : ∃ k, ∃ Z, Z ∈ 𝒮 ∧ Nat.card Z = k := ⟨Nat.card X, X, hXmem, rfl⟩
  obtain ⟨Y, hYmem, hYcard⟩ := Nat.find_spec hex
  refine ⟨Y, W172MinInv.mk hset hYmem.1 hYmem.2.1 hYmem.2.2.1 hYmem.2.2.2 ?_⟩
  intro Z hZY hdZ hsZ hntZ
  have hZmem : Z ∈ 𝒮 := ⟨hZY.trans hYmem.1, hdZ, hsZ, hntZ⟩
  have hle : Nat.card Y ≤ Nat.card Z := by
    have h := Nat.find_min' hex (show ∃ W, W ∈ 𝒮 ∧ Nat.card W = Nat.card Z from ⟨Z, hZmem, rfl⟩)
    rwa [hYcard]
  exact Subgroup.eq_of_le_of_card_ge hZY hle

theorem w172_minInv_gen {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) : Subgroup.closure (W172Inv d Y) = Y := by
  have hd_mul : d * d = 1 := w172_mul_self_eq_one_of_sq_eq_one h.sq
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hYp : IsPGroup p Y := h.pgroup.to_le h.le
  have hYodd : Odd (Nat.card Y) := by
    obtain ⟨n, hn⟩ := hYp.exists_card_eq
    rw [hn]
    exact (h.prime.odd_of_ne_two h.odd).pow
  let J : Subgroup Γ := Subgroup.closure {z : Γ | ∃ y ∈ Y, z = y⁻¹ * (d * y * d⁻¹)}
  have hJ_le_I : J ≤ Subgroup.closure (W172Inv d Y) := by
    rw [Subgroup.closure_le]
    rintro z ⟨y, hy, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · exact Y.mul_mem (Y.inv_mem hy) (h.d_mem y hy)
    · calc d * (y⁻¹ * (d * y * d⁻¹)) * d⁻¹
          = (d * y * d⁻¹)⁻¹ * y := w172_conj_inv_conj_inv_mul hd_mul
        _ = (y⁻¹ * (d * y * d⁻¹))⁻¹ := by group
  have hclosure_le_Y : Subgroup.closure (W172Inv d Y) ≤ Y := by
    rw [Subgroup.closure_le]
    exact fun z hz => hz.1
  have hJ_le_Y : J ≤ Y := hJ_le_I.trans hclosure_le_Y
  have hdJ : ∀ z ∈ J, d * z * d⁻¹ ∈ J := by
    intro z hz
    refine Subgroup.closure_induction (p := fun z _ => d * z * d⁻¹ ∈ J) ?_ ?_ ?_ ?_ hz
    · intro w hw
      obtain ⟨y, hy, rfl⟩ := hw
      rw [w172_conj_inv_conj_inv_mul hd_mul]
      exact Subgroup.subset_closure
        ⟨d * y * d⁻¹, h.d_mem y hy, by rw [w172_conj_conj_eq_self hd_mul]⟩
    · simp
    · intro a b ha hb iha ihb
      rw [show d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) by group]
      exact J.mul_mem iha ihb
    · intro a ha iha
      rw [show d * a⁻¹ * d⁻¹ = (d * a * d⁻¹)⁻¹ by group]
      exact J.inv_mem iha
  have hsJ : ∀ s ∈ S, ∀ z ∈ J, s * z * s⁻¹ ∈ J := by
    intro s hs z hz
    refine Subgroup.closure_induction (p := fun z _ => s * z * s⁻¹ ∈ J) ?_ ?_ ?_ ?_ hz
    · intro w hw
      obtain ⟨y, hy, rfl⟩ := hw
      rw [w172_conj_tau (h.s_comm s hs)]
      exact Subgroup.subset_closure ⟨s * y * s⁻¹, h.s_mem s hs y hy, rfl⟩
    · simp
    · intro a b ha hb iha ihb
      rw [show s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) by group]
      exact J.mul_mem iha ihb
    · intro a ha iha
      rw [show s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ by group]
      exact J.inv_mem iha
  have hntrivJ : ∃ z ∈ J, d * z * d⁻¹ ≠ z := by
    by_contra hcon
    have hfix : ∀ z ∈ J, d * z * d⁻¹ = z := by
      intro z hz
      by_contra hne
      exact hcon ⟨z, hz, hne⟩
    have htriv : ∀ y ∈ Y, d * y * d⁻¹ = y := by
      intro y hy
      have htau_mem : y⁻¹ * (d * y * d⁻¹) ∈ J := Subgroup.subset_closure ⟨y, hy, rfl⟩
      have h1 : d * (y⁻¹ * (d * y * d⁻¹)) * d⁻¹ = y⁻¹ * (d * y * d⁻¹) := hfix _ htau_mem
      have h2 : d * (y⁻¹ * (d * y * d⁻¹)) * d⁻¹ = (y⁻¹ * (d * y * d⁻¹))⁻¹ := by
        calc d * (y⁻¹ * (d * y * d⁻¹)) * d⁻¹
            = (d * y * d⁻¹)⁻¹ * y := w172_conj_inv_conj_inv_mul hd_mul
          _ = (y⁻¹ * (d * y * d⁻¹))⁻¹ := by group
      have htau1 : y⁻¹ * (d * y * d⁻¹) = 1 :=
        w172_eq_one_of_mem_of_inverted_of_fixed hYodd
          (Y.mul_mem (Y.inv_mem hy) (h.d_mem y hy)) h2 h1
      have hty : y⁻¹ * (d * y * d⁻¹) = y⁻¹ * y := by rw [htau1, inv_mul_cancel]
      exact mul_left_cancel hty
    obtain ⟨y, hy, hne⟩ := h.nontriv
    exact hne (htriv y hy)
  have hmin := h.minimal J hJ_le_Y hdJ hsJ hntrivJ
  exact le_antisymm hclosure_le_Y (hmin ▸ hJ_le_I)

theorem w172_minInv_pow_fixed {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) : ∀ y ∈ Y, d * y ^ p * d⁻¹ = y ^ p := by
  have hYp : IsPGroup p Y := h.pgroup.to_le h.le
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (IsPGroup p ↥Y) := ⟨hYp⟩
  haveI : Nontrivial ↥Y := w172_nontrivial_of_minInv h
  let Yp : Subgroup Γ := Subgroup.closure {z : Γ | ∃ y ∈ Y, z = y ^ p}
  have hYp_le_Y : Yp ≤ Y := by
    rw [Subgroup.closure_le]
    rintro z ⟨y, hy, rfl⟩
    exact Y.pow_mem hy p
  have hYp_lt : Yp < Y := by
    have hfr : (frattini ↥Y).map Y.subtype < Y := by
      have hlt := (Subgroup.map_subtype_lt_map_subtype (G' := Y) (H := frattini ↥Y)
        (K := ⊤)).mpr (w172_frattini_lt_top (Y := Y))
      have htop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
        simpa [MonoidHom.range_eq_map] using (Y.range_subtype : Y.subtype.range = Y)
      rwa [htop] at hlt
    have hle : Yp ≤ (frattini ↥Y).map Y.subtype := by
      rw [Subgroup.closure_le]
      rintro z ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩ ^ p,
        CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥Y) (p := p) ⟨y, hy⟩, by simp⟩
    exact lt_of_le_of_lt hle hfr
  have hdYp : ∀ z ∈ Yp, d * z * d⁻¹ ∈ Yp := by
    intro z hz
    refine Subgroup.closure_induction (p := fun z _ => d * z * d⁻¹ ∈ Yp) ?_ ?_ ?_ ?_ hz
    · intro w hw
      obtain ⟨y, hy, rfl⟩ := hw
      rw [← conj_pow]
      exact Subgroup.subset_closure ⟨d * y * d⁻¹, h.d_mem y hy, rfl⟩
    · simp
    · intro a b ha hb iha ihb
      rw [show d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) by group]
      exact Yp.mul_mem iha ihb
    · intro a ha iha
      rw [show d * a⁻¹ * d⁻¹ = (d * a * d⁻¹)⁻¹ by group]
      exact Yp.inv_mem iha
  have hsYp : ∀ s ∈ S, ∀ z ∈ Yp, s * z * s⁻¹ ∈ Yp := by
    intro s hs z hz
    refine Subgroup.closure_induction (p := fun z _ => s * z * s⁻¹ ∈ Yp) ?_ ?_ ?_ ?_ hz
    · intro w hw
      obtain ⟨y, hy, rfl⟩ := hw
      rw [← conj_pow]
      exact Subgroup.subset_closure ⟨s * y * s⁻¹, h.s_mem s hs y hy, rfl⟩
    · simp
    · intro a b ha hb iha ihb
      rw [show s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) by group]
      exact Yp.mul_mem iha ihb
    · intro a ha iha
      rw [show s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ by group]
      exact Yp.inv_mem iha
  have htriv : ∀ z ∈ Yp, d * z * d⁻¹ = z := by
    by_contra hcon
    obtain ⟨z, hz⟩ := not_forall.mp hcon
    obtain ⟨hzYp, hne⟩ := not_imp.mp hz
    exact (ne_of_lt hYp_lt) (h.minimal Yp hYp_le_Y hdYp hsYp ⟨z, hzYp, hne⟩)
  intro y hy
  exact htriv (y ^ p) (Subgroup.subset_closure ⟨y, hy, rfl⟩)

theorem w172_minInv_centralizer {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) :
    ∀ y ∈ Y, d * y * d⁻¹ = y ↔ y ∈ (⁅Y, Y⁆ : Subgroup Γ) := by
  have hd_mul : d * d = 1 := w172_mul_self_eq_one_of_sq_eq_one h.sq
  have hYp : IsPGroup p Y := h.pgroup.to_le h.le
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hYodd : Odd (Nat.card Y) := by
    obtain ⟨n, hn⟩ := hYp.exists_card_eq
    rw [hn]
    exact (h.prime.odd_of_ne_two h.odd).pow
  have hcomm_lt : (⁅Y, Y⁆ : Subgroup Γ) < Y := w172_commutator_lt_self h
  have hY'le : (⁅Y, Y⁆ : Subgroup Γ) ≤ Y := Subgroup.commutator_le_self Y
  have hd_norm : d ∈ Subgroup.normalizer (Y : Set Γ) :=
    w172_mem_normalizer_of_normalizes h.d_mem hd_mul
  have hdYmap : Y.map (MulAut.conj d).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hd_norm
  have hdY' : ∀ z ∈ (⁅Y, Y⁆ : Subgroup Γ), d * z * d⁻¹ ∈ (⁅Y, Y⁆ : Subgroup Γ) := by
    intro z hz
    have hmap : (⁅Y, Y⁆ : Subgroup Γ).map (MulAut.conj d).toMonoidHom = ⁅Y, Y⁆ := by
      rw [Subgroup.map_commutator, hdYmap]
    have : (MulAut.conj d).toMonoidHom z ∈ (⁅Y, Y⁆ : Subgroup Γ) := by
      rw [← hmap]
      exact ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using this
  have hsY' : ∀ s ∈ S, ∀ z ∈ (⁅Y, Y⁆ : Subgroup Γ), s * z * s⁻¹ ∈ (⁅Y, Y⁆ : Subgroup Γ) := by
    intro s hs z hz
    have hs_norm : s ∈ Subgroup.normalizer (Y : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact ⟨h.s_mem s hs y, fun hy => by
        have h2 := h.s_mem s⁻¹ (S.inv_mem hs) (s * y * s⁻¹) hy
        simp only [inv_inv] at h2
        rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h2⟩
    have hsYmap : Y.map (MulAut.conj s).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hs_norm
    have hmap : (⁅Y, Y⁆ : Subgroup Γ).map (MulAut.conj s).toMonoidHom = ⁅Y, Y⁆ := by
      rw [Subgroup.map_commutator, hsYmap]
    have : (MulAut.conj s).toMonoidHom z ∈ (⁅Y, Y⁆ : Subgroup Γ) := by
      rw [← hmap]
      exact ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using this
  have hkey : ∀ y ∈ Y, d * y * d⁻¹ * y ∈ (⁅Y, Y⁆ : Subgroup Γ) := by
    have hclosure : Y = Subgroup.closure (W172Inv d Y) := (w172_minInv_gen h).symm
    intro y hy
    rw [hclosure] at hy
    refine Subgroup.closure_induction (p := fun y _ => d * y * d⁻¹ * y ∈ (⁅Y, Y⁆ : Subgroup Γ))
      ?_ ?_ ?_ ?_ hy
    · intro i hi
      rw [hi.2, inv_mul_cancel]
      exact (⁅Y, Y⁆ : Subgroup Γ).one_mem
    · simp
    · intro a b ha hb iha ihb
      have haY : a ∈ Y := hclosure.symm ▸ ha
      have hbY : b ∈ Y := hclosure.symm ▸ hb
      rw [show d * (a * b) * d⁻¹ * (a * b) =
        (d * a * d⁻¹ * a) * (a⁻¹ * (d * b * d⁻¹ * b) * a) * ⁅a⁻¹, b⁻¹⁆ by
          rw [commutatorElement_def]; group]
      exact (⁅Y, Y⁆ : Subgroup Γ).mul_mem
        ((⁅Y, Y⁆ : Subgroup Γ).mul_mem iha (by
          simpa using w172_mem_commutator_of_conj (Y.inv_mem haY) ihb))
        (Subgroup.commutator_mem_commutator (Y.inv_mem haY) (Y.inv_mem hbY))
    · intro a ha iha
      have haY : a ∈ Y := hclosure.symm ▸ ha
      rw [show d * a⁻¹ * d⁻¹ * a⁻¹ = a * (d * a * d⁻¹ * a)⁻¹ * a⁻¹ by group]
      exact w172_mem_commutator_of_conj haY ((⁅Y, Y⁆ : Subgroup Γ).inv_mem iha)
  intro y hy
  constructor
  · intro hfix
    have hy2 : y ^ 2 ∈ (⁅Y, Y⁆ : Subgroup Γ) := by
      have hh := hkey y hy
      rw [hfix] at hh
      rwa [pow_two]
    have hodd : Odd (orderOf y) := hYodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hy)
    obtain ⟨k, hk⟩ := hodd
    have h2k : (orderOf y + 1) / 2 * 2 = orderOf y + 1 := by omega
    have hy_eq : y = (y ^ 2) ^ ((orderOf y + 1) / 2) := by
      calc y = y ^ (orderOf y + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
        _ = (y ^ 2) ^ ((orderOf y + 1) / 2) := by rw [← pow_mul, mul_comm, h2k]
    rw [hy_eq]
    exact (⁅Y, Y⁆ : Subgroup Γ).pow_mem hy2 _
  · intro hy'
    exact w172_minInv_centralizes_of_ne h hY'le hdY' hsY' (ne_of_lt hcomm_lt) y hy'

theorem w172_minInv_transversal {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) :
    ∀ y ∈ Y, ∃! z : Γ, z ∈ W172Inv d Y ∧ z⁻¹ * y ∈ (⁅Y, Y⁆ : Subgroup Γ) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hYp : IsPGroup p Y := h.pgroup.to_le h.le
  have hYodd : Odd (Nat.card Y) := by
    obtain ⟨n, hn⟩ := hYp.exists_card_eq
    rw [hn]
    exact (h.prime.odd_of_ne_two h.odd).pow
  have hd_mul : d * d = 1 := w172_mul_self_eq_one_of_sq_eq_one h.sq
  have hd_norm : d ∈ Subgroup.normalizer (Y : Set Γ) :=
    w172_mem_normalizer_of_normalizes h.d_mem hd_mul
  have hd_ne_one : d ≠ 1 := by
    obtain ⟨y, hy, hne⟩ := h.nontriv
    intro hd1
    exact hne (by rw [hd1]; simp)
  have hd_order : orderOf d = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime h.sq hd_ne_one
  have hbij := CFSG.OddInversion.inverted_mul_fixed_bijOn (A := Y) (t := d) hYodd hd_order hd_norm
  intro y hy
  obtain ⟨⟨z, c⟩, ⟨hz, hc⟩, hzc⟩ := hbij.surjOn hy
  have hcY : c ∈ Y := (Subgroup.mem_inf.mp hc).1
  have hcfix : d * c * d⁻¹ = c := by
    have hcd : c * d = d * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    rw [← hcd, mul_assoc, mul_inv_cancel, mul_one]
  have hcY' : c ∈ (⁅Y, Y⁆ : Subgroup Γ) := (w172_minInv_centralizer h c hcY).mp hcfix
  have hzy : z⁻¹ * y = c := by rw [← hzc]; group
  refine ⟨z, ⟨hz, ?_⟩, ?_⟩
  · rw [hzy]; exact hcY'
  · intro w hw
    obtain ⟨hwI, hwY'⟩ := hw
    have hcwY : w⁻¹ * y ∈ Y := (Subgroup.commutator_le_self Y) hwY'
    have hcwfix : d * (w⁻¹ * y) * d⁻¹ = w⁻¹ * y :=
      (w172_minInv_centralizer h (w⁻¹ * y) hcwY).mpr hwY'
    have hw_dom : (w, w⁻¹ * y) ∈
        CFSG.OddInversion.invertedSet Y d ×ˢ
          ((Y ⊓ Subgroup.centralizer {d} : Subgroup Γ) : Set Γ) := by
      refine ⟨hwI, ?_⟩
      change w⁻¹ * y ∈ (Y ⊓ Subgroup.centralizer {d} : Subgroup Γ)
      rw [Subgroup.mem_inf]
      refine ⟨hcwY, ?_⟩
      change w⁻¹ * y ∈ Subgroup.centralizer {d}
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (w⁻¹ * y) * d = d * (w⁻¹ * y) * d⁻¹ * d := by rw [hcwfix]
        _ = d * (w⁻¹ * y) := by group
    have hz_dom : (z, c) ∈
        CFSG.OddInversion.invertedSet Y d ×ˢ
          ((Y ⊓ Subgroup.centralizer {d} : Subgroup Γ) : Set Γ) := ⟨hz, hc⟩
    have heq : (fun x : Γ × Γ => x.1 * x.2) (w, w⁻¹ * y) =
        (fun x : Γ × Γ => x.1 * x.2) (z, c) := by
      simp only
      rw [← hzc]
      group
    exact congrArg Prod.fst (hbij.injOn hw_dom hz_dom heq)

theorem w172_minInv_center {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) (hY : (⁅Y, Y⁆ : Subgroup Γ) ≠ ⊥) :
    ∀ z ∈ Y, (∀ y ∈ Y, y * z = z * y) → z ∈ (⁅Y, Y⁆ : Subgroup Γ) := by
  intro z hzY hzcentral
  have hdz : d * z * d⁻¹ = z := by
    have hZY : (Subgroup.center ↥Y).map Y.subtype ≤ Y := by
      intro w hw
      obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hw
      exact u.2
    have hdZ : ∀ w ∈ (Subgroup.center ↥Y).map Y.subtype,
        d * w * d⁻¹ ∈ (Subgroup.center ↥Y).map Y.subtype := by
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
      refine Subgroup.mem_map.mpr ⟨⟨d * (u : Γ) * d⁻¹, h.d_mem u u.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro v
      apply Subtype.ext
      have hv : d⁻¹ * (v : Γ) * d ∈ Y := by
        simpa [w172_inv_eq_self_of_sq_eq_one h.sq] using h.d_mem (v : Γ) v.2
      have hcu := Subgroup.mem_center_iff.mp hu ⟨d⁻¹ * (v : Γ) * d, hv⟩
      have hcuv : (d⁻¹ * (v : Γ) * d) * (u : Γ) = (u : Γ) * (d⁻¹ * (v : Γ) * d) :=
        congrArg Subtype.val hcu
      show (v : Γ) * (d * (u : Γ) * d⁻¹) = (d * (u : Γ) * d⁻¹) * (v : Γ)
      calc (v : Γ) * (d * (u : Γ) * d⁻¹)
          = d * ((d⁻¹ * (v : Γ) * d) * (u : Γ)) * d⁻¹ := by group
        _ = d * ((u : Γ) * (d⁻¹ * (v : Γ) * d)) * d⁻¹ := by rw [hcuv]
        _ = (d * (u : Γ) * d⁻¹) * (v : Γ) := by group
    have hsZ : ∀ s ∈ S, ∀ w ∈ (Subgroup.center ↥Y).map Y.subtype,
        s * w * s⁻¹ ∈ (Subgroup.center ↥Y).map Y.subtype := by
      intro s hs w hw
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
      refine Subgroup.mem_map.mpr ⟨⟨s * (u : Γ) * s⁻¹, h.s_mem s hs u u.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro v
      apply Subtype.ext
      have hv : s⁻¹ * (v : Γ) * s ∈ Y := by
        simpa using h.s_mem s⁻¹ (S.inv_mem hs) (v : Γ) v.2
      have hcu := Subgroup.mem_center_iff.mp hu ⟨s⁻¹ * (v : Γ) * s, hv⟩
      have hcuv : (s⁻¹ * (v : Γ) * s) * (u : Γ) = (u : Γ) * (s⁻¹ * (v : Γ) * s) :=
        congrArg Subtype.val hcu
      show (v : Γ) * (s * (u : Γ) * s⁻¹) = (s * (u : Γ) * s⁻¹) * (v : Γ)
      calc (v : Γ) * (s * (u : Γ) * s⁻¹)
          = s * ((s⁻¹ * (v : Γ) * s) * (u : Γ)) * s⁻¹ := by group
        _ = s * ((u : Γ) * (s⁻¹ * (v : Γ) * s)) * s⁻¹ := by rw [hcuv]
        _ = (s * (u : Γ) * s⁻¹) * (v : Γ) := by group
    have hZne : (Subgroup.center ↥Y).map Y.subtype ≠ Y := by
      intro heq
      have htop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
        simpa [MonoidHom.range_eq_map] using (Y.range_subtype : Y.subtype.range = Y)
      have hZc_top : Subgroup.center ↥Y = ⊤ :=
        Subgroup.map_injective Y.subtype_injective (by rw [heq, htop])
      have hcomm : IsMulCommutative ↥Y := Subgroup.center_eq_top_iff.mp hZc_top
      exact hY (Subgroup.commutator_self_eq_bot_iff.mpr hcomm)
    have hzZ : z ∈ (Subgroup.center ↥Y).map Y.subtype := by
      refine Subgroup.mem_map.mpr ⟨⟨z, hzY⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro u
      exact Subtype.ext (hzcentral u u.2)
    exact w172_minInv_centralizes_of_ne h hZY hdZ hsZ hZne z hzZ
  exact (w172_minInv_centralizer h z hzY).mp hdz

theorem w172_minInv_card {p : ℕ} {X : Subgroup Γ} {d : Γ} {S Y : Subgroup Γ}
    (h : W172MinInv p X d S Y) :
    ∃ a : ℕ, 1 ≤ a ∧ Nat.card Y = p ^ a * Nat.card (⁅Y, Y⁆ : Subgroup Γ) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hYp : IsPGroup p Y := h.pgroup.to_le h.le
  have hY'le : (⁅Y, Y⁆ : Subgroup Γ) ≤ Y := Subgroup.commutator_le_self Y
  have hcomm_lt : (⁅Y, Y⁆ : Subgroup Γ) < Y := w172_commutator_lt_self h
  have hrel_dvd : (⁅Y, Y⁆ : Subgroup Γ).relIndex Y ∣ Nat.card Y := by
    have hh := Subgroup.relIndex_mul_card (H := (⁅Y, Y⁆ : Subgroup Γ)) (K := Y)
    rw [inf_eq_left.mpr hY'le] at hh
    exact ⟨Nat.card (⁅Y, Y⁆ : Subgroup Γ), hh.symm⟩
  obtain ⟨n, hn⟩ := hYp.exists_card_eq
  have hrel_dvd' : (⁅Y, Y⁆ : Subgroup Γ).relIndex Y ∣ p ^ n := by rwa [hn] at hrel_dvd
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow h.prime).mp hrel_dvd'
  refine ⟨a, ?_, ?_⟩
  · by_contra ha0
    have ha0' : a = 0 := by omega
    have hone : (⁅Y, Y⁆ : Subgroup Γ).relIndex Y = 1 := by rw [ha, ha0']; simp
    have hle : Y ≤ (⁅Y, Y⁆ : Subgroup Γ) := Subgroup.relIndex_eq_one.mp hone
    exact hcomm_lt.ne (le_antisymm hle hY'le).symm
  · have hh := Subgroup.relIndex_mul_card (H := (⁅Y, Y⁆ : Subgroup Γ)) (K := Y)
    rw [inf_eq_left.mpr hY'le, ha] at hh
    exact hh.symm

end CFSG.LocalAnalysis.WeakClosure81

end
