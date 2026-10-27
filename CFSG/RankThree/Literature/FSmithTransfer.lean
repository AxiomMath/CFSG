module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.Literature.FSmith

open Subgroup MulAction
open scoped commutatorElement

variable {G : Type*} [Group G]

section Tau

variable {H : Subgroup G} (ϕ : H →* Multiplicative (ZMod 2)) (a : G)

@[expose] noncomputable def tau (X : G ⧸ H) : Multiplicative (ZMod 2) :=
  open _root_.Classical in
  if h : (Quotient.out X)⁻¹ * a * Quotient.out X ∈ H then ϕ ⟨_, h⟩ else 1

variable {a}

theorem smul_mk_eq_iff {x : G} : a • (x : G ⧸ H) = x ↔ x⁻¹ * a * x ∈ H := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
  have e : (a * x)⁻¹ * x = (x⁻¹ * a * x)⁻¹ := by group
  rw [e, inv_mem_iff]

theorem tau_mk {x : G} (hx : x⁻¹ * a * x ∈ H) : tau ϕ a (x : G ⧸ H) = ϕ ⟨_, hx⟩ := by
  obtain ⟨h, hh⟩ : ∃ h : H, Quotient.out (x : G ⧸ H) = x * h := by
    have := QuotientGroup.leftRel_apply.mp (Quotient.exact (Quotient.out_eq (x : G ⧸ H)))
    exact ⟨⟨x⁻¹ * Quotient.out (x : G ⧸ H), by simpa using inv_mem this⟩, by simp⟩
  have hmem : (Quotient.out (x : G ⧸ H))⁻¹ * a * Quotient.out (x : G ⧸ H) ∈ H := by
    rw [hh]
    have : (x * h)⁻¹ * a * (x * h) = (h : G)⁻¹ * (x⁻¹ * a * x) * h := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem h.2) hx) h.2
  unfold tau
  simp only [hmem, ↓reduceDIte]
  have : (⟨_, hmem⟩ : H) = h⁻¹ * ⟨_, hx⟩ * h := by
    apply Subtype.ext
    simp only [hh, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [this, map_mul, map_mul, mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one,
    one_mul]

theorem eq_of_mem_orbit_zpowers {α : Type*} [MulAction G α] {X Y : α}
    (hY : Y ∈ orbit (zpowers a) X) (hX : a • X = X) : Y = X := by
  obtain ⟨⟨g, hg⟩, rfl⟩ := hY
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have ha : a ∈ stabilizer G X := hX
  exact (stabilizer G X).zpow_mem ha k

theorem transfer_eq_prod_fixed [Finite G] [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)]
    (ha2 : a * a = 1) :
    ϕ.transfer a = ∏ X : G ⧸ H, (if a • X = X then tau ϕ a X else 1) := by
  classical
  have : Fintype (Quotient (orbitRel (zpowers a) (G ⧸ H))) := Fintype.ofFinite _
  rw [ϕ.transfer_eq_prod_quotient_orbitRel_zpowers_quot a,
    ← Finset.prod_fiberwise Finset.univ
      (fun X : G ⧸ H => (Quotient.mk'' X : Quotient (orbitRel (zpowers a) (G ⧸ H))))]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hfib : ∀ X : G ⧸ H,
      (Quotient.mk'' X : Quotient (orbitRel (zpowers a) (G ⧸ H))) = q ↔
        X ∈ orbit (zpowers a) (Quotient.out q) := by
    intro X
    conv_lhs => rw [← Quotient.out_eq q]
    rw [Quotient.mk''_eq_mk, Quotient.eq, orbitRel_apply]
  have hmem : (Quotient.out (Quotient.out q))⁻¹ * a * Quotient.out (Quotient.out q) ∈ H ↔
      a • Quotient.out q = Quotient.out q := by
    rw [← smul_mk_eq_iff, QuotientGroup.out_eq']
  by_cases hX₀ : a • Quotient.out q = Quotient.out q
  · have hper : Function.minimalPeriod (fun x => a • x) (Quotient.out q) = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hX₀
    have hfiber : (Finset.univ.filter fun X : G ⧸ H =>
        (Quotient.mk'' X : Quotient (orbitRel (zpowers a) (G ⧸ H))) = q) = {Quotient.out q} := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hfib]
      exact ⟨fun h => eq_of_mem_orbit_zpowers h hX₀, fun h => h ▸ mem_orbit_self _⟩
    rw [hfiber, Finset.prod_singleton, ite_eq_left hX₀]
    have h1 := hmem.mpr hX₀
    have e : tau ϕ a (Quotient.out q) = ϕ ⟨_, h1⟩ := by
      have := tau_mk ϕ h1
      rwa [QuotientGroup.out_eq'] at this
    rw [e]
    congr 2
    rw [hper, pow_one]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hper : Function.minimalPeriod (fun x => a • x) (Quotient.out q) = 2 := by
      refine Function.minimalPeriod_eq_prime ?_ hX₀
      change (fun x => a • x)^[2] (Quotient.out q) = Quotient.out q
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
      rw [smul_smul, ha2, one_smul]
    have hone : ∀ X ∈ Finset.univ.filter fun X : G ⧸ H =>
        (Quotient.mk'' X : Quotient (orbitRel (zpowers a) (G ⧸ H))) = q,
        (if a • X = X then tau ϕ a X else 1) = 1 := by
      intro X hX
      rw [Finset.mem_filter, hfib] at hX
      rw [ite_eq_right]
      intro hfix
      apply hX₀
      have hsymm : Quotient.out q ∈ orbit (zpowers a) X := mem_orbit_symm.mpr hX.2
      rw [eq_of_mem_orbit_zpowers hsymm hfix]
      exact hfix
    rw [Finset.prod_eq_one hone]
    have hsq : (Quotient.out (Quotient.out q))⁻¹ * a ^ 2 * Quotient.out (Quotient.out q) = 1 := by
      rw [pow_two, ha2, mul_one, inv_mul_cancel]
    rw [← map_one ϕ]
    congr 1
    apply Subtype.ext
    simp only [hper, hsq, OneMemClass.coe_one]

theorem even_card_of_transfer_eq_one [Finite G] [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)]
    (ha2 : a * a = 1) (hV : ϕ.transfer a = 1) :
    Even (Finset.univ.filter fun X : G ⧸ H => a • X = X ∧ tau ϕ a X ≠ 1).card := by
  classical
  rw [transfer_eq_prod_fixed ϕ ha2] at hV
  have hval : ∀ X : G ⧸ H, (if a • X = X then tau ϕ a X else 1) =
      Multiplicative.ofAdd (if a • X = X ∧ tau ϕ a X ≠ 1 then (1 : ZMod 2) else 0) := by
    intro X
    by_cases hX : a • X = X
    · rw [ite_eq_left hX]
      by_cases ht : tau ϕ a X = 1
      · rw [ite_eq_right (fun h => h.2 ht), ht, ofAdd_zero]
      · rw [ite_eq_left ⟨hX, ht⟩]
        have : Multiplicative.toAdd (tau ϕ a X) ≠ 0 := fun h => ht (by
          rw [← ofAdd_toAdd (tau ϕ a X), h, ofAdd_zero])
        rw [← ofAdd_toAdd (tau ϕ a X)]
        congr 1
        revert this
        generalize Multiplicative.toAdd (tau ϕ a X) = c
        revert c
        decide
    · rw [ite_eq_right hX, ite_eq_right (fun h => hX h.1), ofAdd_zero]
  simp only [hval] at hV
  rw [← ofAdd_sum, Finset.sum_boole, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
    ZMod.natCast_eq_zero_iff_even] at hV
  exact hV

end Tau

theorem even_card_of_involution {α : Type*} [DecidableEq α] {s : Finset α} (σ : α → α)
    (hmaps : ∀ x ∈ s, σ x ∈ s) (hinv : ∀ x ∈ s, σ (σ x) = x) (hne : ∀ x ∈ s, σ x ≠ x) :
    Even s.card := by
  let τ : Equiv.Perm s :=
    { toFun := fun x => ⟨σ x, hmaps x x.2⟩
      invFun := fun x => ⟨σ x, hmaps x x.2⟩
      left_inv := fun x => Subtype.ext (hinv x x.2)
      right_inv := fun x => Subtype.ext (hinv x x.2) }
  have h2 : τ ^ 2 = 1 := by
    ext x
    simp [τ, pow_two, hinv x x.2]
  have hsupp : τ.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    intro h
    exact hne x x.2 (congrArg Subtype.val h)
  have h := Equiv.Perm.two_dvd_card_support h2
  rw [hsupp, Finset.card_univ, Fintype.card_coe] at h
  exact even_iff_two_dvd.mpr h

section Smith

variable {z : G} (ϕ : centralizer ({z} : Set G) →* Multiplicative (ZMod 2)) {F : Subgroup G}
  {a : G}

theorem eq_one_of_forall_smul_eq (hz : z ≠ 1)
    (hCF : ∀ c : G, (∀ f ∈ F, c * f = f * c) → c = 1 ∨ c = z) {X : G ⧸ centralizer ({z} : Set G)}
    (hX : ∀ f ∈ F, f • X = X) : X = ((1 : G) : G ⧸ centralizer ({z} : Set G)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective X
  have hc : ∀ f ∈ F, (x * z * x⁻¹) * f = f * (x * z * x⁻¹) := by
    intro f hf
    have h1 := smul_mk_eq_iff.mp (hX f hf)
    have h2 := mem_centralizer_singleton_iff.mp h1
    calc x * z * x⁻¹ * f = x * (z * (x⁻¹ * f * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * f * x) * z) * x⁻¹ := by rw [h2]
      _ = f * (x * z * x⁻¹) := by group
  rcases hCF _ hc with h | h
  · exfalso
    apply hz
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, h]
    group
  · rw [QuotientGroup.eq, mul_one, inv_mem_iff, mem_centralizer_singleton_iff]
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [h]

theorem smul_one_coset {h : G} (hh : h ∈ centralizer ({z} : Set G)) :
    h • ((1 : G) : G ⧸ centralizer ({z} : Set G)) = ((1 : G) : G ⧸ centralizer ({z} : Set G)) := by
  rw [smul_mk_eq_iff, inv_one, one_mul, mul_one]
  exact hh

theorem tau_one_coset (ha : a ∈ centralizer ({z} : Set G)) :
    tau ϕ a ((1 : G) : G ⧸ centralizer ({z} : Set G)) = ϕ ⟨a, ha⟩ := by
  have h1 : (1 : G)⁻¹ * a * 1 ∈ centralizer ({z} : Set G) := by
    rw [inv_one, one_mul, mul_one]
    exact ha
  rw [tau_mk ϕ h1]
  congr 1
  apply Subtype.ext
  simp

theorem tau_smul_of_commute {w : G} (hw : w * a = a * w) {X : G ⧸ centralizer ({z} : Set G)}
    (hX : a • X = X) : a • w • X = w • X ∧ tau ϕ a (w • X) = tau ϕ a X := by
  refine ⟨by rw [smul_smul, ← hw, mul_smul, hX], ?_⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective X
  have h0 : y⁻¹ * a * y ∈ centralizer ({z} : Set G) := smul_mk_eq_iff.mp hX
  have e : (w * y)⁻¹ * a * (w * y) = y⁻¹ * a * y := by
    have hwa : w⁻¹ * a * w = a := by rw [mul_assoc, ← hw, inv_mul_cancel_left]
    calc (w * y)⁻¹ * a * (w * y) = y⁻¹ * (w⁻¹ * a * w) * y := by group
      _ = y⁻¹ * a * y := by rw [hwa]
  have h1 : (w * y)⁻¹ * a * (w * y) ∈ centralizer ({z} : Set G) := by rw [e]; exact h0
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, tau_mk ϕ h1, tau_mk ϕ h0]
  congr 1
  exact Subtype.ext e

theorem tau_smul_of_conj_eq {e y : G} (he : e⁻¹ * a * e = a * z)
    (ha : y⁻¹ * a * y ∈ centralizer ({z} : Set G)) (hz : y⁻¹ * z * y ∈ centralizer ({z} : Set G))
    (hϕz : ϕ ⟨_, hz⟩ = 1) :
    a • e • (y : G ⧸ centralizer ({z} : Set G)) = e • (y : G ⧸ centralizer ({z} : Set G)) ∧
      tau ϕ a (e • (y : G ⧸ centralizer ({z} : Set G))) = tau ϕ a y := by
  have e1 : (e * y)⁻¹ * a * (e * y) = (y⁻¹ * a * y) * (y⁻¹ * z * y) := by
    calc (e * y)⁻¹ * a * (e * y) = y⁻¹ * (e⁻¹ * a * e) * y := by group
      _ = (y⁻¹ * a * y) * (y⁻¹ * z * y) := by rw [he]; group
  have h1 : (e * y)⁻¹ * a * (e * y) ∈ centralizer ({z} : Set G) := by
    rw [e1]
    exact mul_mem ha hz
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  refine ⟨smul_mk_eq_iff.mpr h1, ?_⟩
  rw [tau_mk ϕ h1, tau_mk ϕ ha]
  have : (⟨_, h1⟩ : centralizer ({z} : Set G)) = ⟨_, ha⟩ * ⟨_, hz⟩ := Subtype.ext e1
  rw [this, map_mul, hϕz, mul_one]

theorem exists_pairing [Finite G] (hz : z ≠ 1) (hz2 : z * z = 1)
    (hFH : F ≤ centralizer ({z} : Set G)) (hF2 : IsPGroup 2 F)
    (hCF : ∀ c : G, (∀ f ∈ F, c * f = f * c) → c = 1 ∨ c = z) (haF : a ∈ F)
    (hFa : ∀ f ∈ F, f * a * f⁻¹ = a ∨ f * a * f⁻¹ = a * z) (he : ∃ e ∈ F, e * a * e⁻¹ = a * z)
    (hc : ∃ c₁ ∈ F, ∃ c₂ ∈ F, c₁ * a = a * c₁ ∧ c₂ * a = a * c₂ ∧ ⁅c₁, c₂⁆ = z)
    {X : G ⧸ centralizer ({z} : Set G)} (hX : X ≠ ((1 : G) : G ⧸ centralizer ({z} : Set G))) :
    ∃ w ∈ F, ∀ Y ∈ orbit F X, w • w • Y = Y ∧ w • Y ≠ Y ∧
      (a • Y = Y → a • w • Y = w • Y ∧ tau ϕ a (w • Y) = tau ϕ a Y) := by
  classical
  have hzc : ∀ f ∈ F, f * z = z * f := fun f hf => mem_centralizer_singleton_iff.mp (hFH hf)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzconj : ∀ f ∈ F, f⁻¹ * z * f = z := fun f hf => by
    rw [mul_assoc, ← hzc f hf, inv_mul_cancel_left]
  have hconj : ∀ f ∈ F, f * a * f⁻¹ = a * z → f⁻¹ * a * f = a * z := by
    intro f hf h
    have h2 : (f⁻¹ * a * f) * z = a := by
      calc (f⁻¹ * a * f) * z = (f⁻¹ * a * f) * (f⁻¹ * z * f) := by rw [hzconj f hf]
        _ = f⁻¹ * (a * z) * f := by group
        _ = f⁻¹ * (f * a * f⁻¹) * f := by rw [h]
        _ = a := by group
    rw [eq_mul_inv_of_mul_eq h2, hzinv]
  have horb : ∀ Y ∈ orbit F X, Y ≠ ((1 : G) : G ⧸ centralizer ({z} : Set G)) := by
    intro Y hY hY1
    obtain ⟨⟨f, hf⟩, rfl⟩ := mem_orbit_iff.mp hY
    apply hX
    have : X = f⁻¹ • ((⟨f, hf⟩ : F) • X) := by
      rw [Subgroup.smul_def]
      exact (inv_smul_smul f X).symm
    rw [this, hY1, smul_one_coset (hFH (inv_mem hf))]
  by_cases hcase : ∀ c ∈ F, c * a = a * c → ∀ Y ∈ orbit F X, c • Y = Y
  ·
    obtain ⟨e, heF, hea⟩ := he
    obtain ⟨c₁, hc₁F, c₂, hc₂F, hc₁a, hc₂a, hcz⟩ := hc
    have hzF : z ∈ F := by
      rw [← hcz, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hc₁F hc₂F) (inv_mem hc₁F)) (inv_mem hc₂F)
    have hzY : ∀ Y ∈ orbit F X, z • Y = Y := hcase z hzF (hzc a haF).symm
    have hee : (e * e) * a = a * (e * e) := by
      have h1 : e * z * e⁻¹ = z := by rw [hzc e heF, mul_inv_cancel_right]
      have h2 : (e * e) * a * (e * e)⁻¹ = a := by
        calc (e * e) * a * (e * e)⁻¹ = e * (e * a * e⁻¹) * e⁻¹ := by group
          _ = e * (a * z) * e⁻¹ := by rw [hea]
          _ = (e * a * e⁻¹) * (e * z * e⁻¹) := by group
          _ = a := by rw [hea, h1, mul_assoc, hz2, mul_one]
      calc (e * e) * a = (e * e) * a * (e * e)⁻¹ * (e * e) := by group
        _ = a * (e * e) := by rw [h2]
    have he' : e⁻¹ * a * e = a * z := hconj e heF hea
    refine ⟨e, heF, fun Y hY => ⟨?_, ?_, fun haY => ?_⟩⟩
    · rw [smul_smul]
      exact hcase _ (mul_mem heF heF) hee Y hY
    · intro hfix
      have hall : ∀ f ∈ F, f • Y = Y := by
        intro f hf
        rcases hFa f hf with h | h
        · have hfa : f * a = a * f := by
            calc f * a = f * a * f⁻¹ * f := by group
              _ = a * f := by rw [h]
          exact hcase f hf hfa Y hY
        · have hf' := hconj f hf h
          have h4 : (e⁻¹ * f)⁻¹ * a * (e⁻¹ * f) = a := by
            calc (e⁻¹ * f)⁻¹ * a * (e⁻¹ * f) = f⁻¹ * (e * a * e⁻¹) * f := by group
              _ = (f⁻¹ * a * f) * (f⁻¹ * z * f) := by rw [hea]; group
              _ = a := by rw [hf', hzconj f hf, mul_assoc, hz2, mul_one]
          have hef : (e⁻¹ * f) * a = a * (e⁻¹ * f) := by
            calc (e⁻¹ * f) * a = (e⁻¹ * f) * ((e⁻¹ * f)⁻¹ * a * (e⁻¹ * f)) := by rw [h4]
              _ = a * (e⁻¹ * f) := by group
          have h5 := hcase _ (mul_mem (inv_mem heF) hf) hef Y hY
          calc f • Y = e • (e⁻¹ * f) • Y := by rw [smul_smul, mul_inv_cancel_left]
            _ = e • Y := by rw [h5]
            _ = Y := hfix
      exact horb Y hY (eq_one_of_forall_smul_eq hz hCF hall)
    · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective Y
      have ha0 : y⁻¹ * a * y ∈ centralizer ({z} : Set G) := smul_mk_eq_iff.mp haY
      have hz0 : y⁻¹ * z * y ∈ centralizer ({z} : Set G) := smul_mk_eq_iff.mp (hzY _ hY)
      have hc₁0 : y⁻¹ * c₁ * y ∈ centralizer ({z} : Set G) :=
        smul_mk_eq_iff.mp (hcase c₁ hc₁F hc₁a _ hY)
      have hc₂0 : y⁻¹ * c₂ * y ∈ centralizer ({z} : Set G) :=
        smul_mk_eq_iff.mp (hcase c₂ hc₂F hc₂a _ hY)
      have hϕz : ϕ ⟨_, hz0⟩ = 1 := by
        have e2 : y⁻¹ * z * y = (y⁻¹ * c₁ * y) * (y⁻¹ * c₂ * y) * (y⁻¹ * c₁ * y)⁻¹ *
            (y⁻¹ * c₂ * y)⁻¹ := by
          rw [← hcz, commutatorElement_def]
          group
        have : (⟨_, hz0⟩ : centralizer ({z} : Set G)) =
            ⁅(⟨_, hc₁0⟩ : centralizer ({z} : Set G)), ⟨_, hc₂0⟩⁆ := by
          apply Subtype.ext
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
          exact e2
        rw [this, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
      exact tau_smul_of_conj_eq ϕ he' ha0 hz0 hϕz
  ·
    simp only [not_forall] at hcase
    obtain ⟨c, hcF, hca, Y₀, hY₀, hcY₀⟩ := hcase
    let π : F →* Equiv.Perm (orbit F X) := MulAction.toPermHom F (orbit F X)
    let A : Subgroup F := (centralizer ({a} : Set G)).subgroupOf F
    have hmemA : ∀ f : F, f ∈ A ↔ (f : G) * a = a * f := fun f => by
      rw [Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    have hAn : A.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [hmemA] at hn ⊢
      have hb : (g : G)⁻¹ * a * g = a ∨ (g : G)⁻¹ * a * g = a * z := by
        have h := hFa _ (inv_mem g.2)
        rwa [inv_inv] at h
      have hnb : (n : G) * ((g : G)⁻¹ * a * g) = ((g : G)⁻¹ * a * g) * n := by
        rcases hb with h | h <;> rw [h]
        · exact hn
        · rw [← mul_assoc, hn, mul_assoc, hzc n n.2, ← mul_assoc]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (g : G) * n * (g : G)⁻¹ * a = g * (n * ((g : G)⁻¹ * a * g)) * (g : G)⁻¹ := by group
        _ = g * (((g : G)⁻¹ * a * g) * n) * (g : G)⁻¹ := by rw [hnb]
        _ = a * (g * n * (g : G)⁻¹) := by group
    let N : Subgroup π.range := A.map π.rangeRestrict
    have hNn : N.Normal := hAn.map _ π.rangeRestrict_surjective
    have hcN : π.rangeRestrict ⟨c, hcF⟩ ∈ N := Subgroup.mem_map_of_mem _ ((hmemA _).mpr hca)
    have hcne : π.rangeRestrict ⟨c, hcF⟩ ≠ 1 := by
      intro h1
      apply hcY₀
      have h2 := congrArg (fun p : π.range =>
        (((p : Equiv.Perm (orbit F X)) ⟨Y₀, hY₀⟩ : orbit F X) : G ⧸ centralizer ({z} : Set G))) h1
      exact h2
    have hNne : N ≠ ⊥ := fun hbot => hcne (by rw [hbot] at hcN; exact Subgroup.mem_bot.mp hcN)
    have hP2 : IsPGroup 2 π.range := hF2.of_surjective _ π.rangeRestrict_surjective
    have : Group.IsNilpotent π.range := hP2.isNilpotent
    have hNZ : N ⊓ center π.range ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hNne
    have hdvd : 2 ∣ Nat.card (N ⊓ center π.range : Subgroup π.range) := by
      rcases (hP2.to_subgroup (N ⊓ center π.range)).card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hNZ
      · exact h
    obtain ⟨⟨g, hg⟩, hgord⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(N ⊓ center π.range)) 2 hdvd
    have hgord' : orderOf g = 2 := (Subgroup.orderOf_coe ⟨g, hg⟩).trans hgord
    obtain ⟨hgN, hgZ⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨w', hw'A, hw'g⟩ := Subgroup.mem_map.mp hgN
    have hwa : (w' : G) * a = a * w' := (hmemA w').mp hw'A
    have hg1 : g ≠ 1 := fun h => by
      rw [h, orderOf_one] at hgord'
      exact absurd hgord' (by norm_num)
    have hg2 : g * g = 1 := by rw [← pow_two, ← hgord', pow_orderOf_eq_one]
    have hgw : (g : Equiv.Perm (orbit F X)) = π w' := by rw [← hw'g]; rfl
    refine ⟨w', w'.2, fun Y hY => ⟨?_, ?_, fun haY => tau_smul_of_commute ϕ hwa haY⟩⟩
    · have h := congrArg (fun p : π.range =>
        (((p : Equiv.Perm (orbit F X)) ⟨Y, hY⟩ : orbit F X) : G ⧸ centralizer ({z} : Set G))) hg2
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hgw, OneMemClass.coe_one,
        Equiv.Perm.one_apply] at h
      exact h
    · intro hfix
      apply hg1
      apply Subtype.ext
      rw [hgw]
      refine Equiv.ext fun Y' => Subtype.ext ?_
      obtain ⟨Y', hY'⟩ := Y'
      have hY'' : Y' ∈ orbit F Y := by rw [orbit_eq_iff.mpr hY]; exact hY'
      obtain ⟨f, rfl⟩ := mem_orbit_iff.mp hY''
      have hcomm := Subgroup.mem_center_iff.mp hgZ (π.rangeRestrict f)
      have h := congrArg (fun p : π.range =>
        (((p : Equiv.Perm (orbit F X)) ⟨Y, hY⟩ : orbit F X) :
          G ⧸ centralizer ({z} : Set G))) hcomm
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hgw] at h
      change (w' : G) • (f : G) • Y = (f : G) • Y
      change (f : G) • (w' : G) • Y = (w' : G) • (f : G) • Y at h
      rw [← h, hfix]

theorem smith_transfer [Finite G] (hz : z ≠ 1) (hz2 : z * z = 1)
    (hFH : F ≤ centralizer ({z} : Set G)) (hF2 : IsPGroup 2 F)
    (hCF : ∀ c : G, (∀ f ∈ F, c * f = f * c) → c = 1 ∨ c = z) (haF : a ∈ F) (ha2 : a * a = 1)
    (hϕa : ϕ ⟨a, hFH haF⟩ ≠ 1) (hV : ϕ.transfer a = 1)
    (hFa : ∀ f ∈ F, f * a * f⁻¹ = a ∨ f * a * f⁻¹ = a * z) (he : ∃ e ∈ F, e * a * e⁻¹ = a * z)
    (hc : ∃ c₁ ∈ F, ∃ c₂ ∈ F, c₁ * a = a * c₁ ∧ c₂ * a = a * c₂ ∧ ⁅c₁, c₂⁆ = z) : False := by
  classical
  have : Fintype (G ⧸ centralizer ({z} : Set G)) := Fintype.ofFinite _
  set H₀ : G ⧸ centralizer ({z} : Set G) := ((1 : G) : G ⧸ centralizer ({z} : Set G)) with hH₀def
  set S := Finset.univ.filter fun X : G ⧸ centralizer ({z} : Set G) => a • X = X ∧ tau ϕ a X ≠ 1
    with hSdef
  have hS : Even S.card := even_card_of_transfer_eq_one ϕ ha2 hV
  have hH₀ : H₀ ∈ S := by
    rw [hSdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, smul_one_coset (hFH haF), ?_⟩
    rw [hH₀def, tau_one_coset ϕ (hFH haF)]
    exact hϕa
  let good : Set (G ⧸ centralizer ({z} : Set G)) → G → Prop := fun O w =>
    w ∈ F ∧ ∀ Y ∈ O, w • w • Y = Y ∧ w • Y ≠ Y ∧
      (a • Y = Y → a • w • Y = w • Y ∧ tau ϕ a (w • Y) = tau ϕ a Y)
  let pick : Set (G ⧸ centralizer ({z} : Set G)) → G := fun O =>
    if h : ∃ w, good O w then h.choose else 1
  have hpick : ∀ X, X ≠ H₀ → good (orbit F X) (pick (orbit F X)) := by
    intro X hX
    have hex : ∃ w, good (orbit F X) w := by
      obtain ⟨w, hwF, hw⟩ := exists_pairing ϕ hz hz2 hFH hF2 hCF haF hFa he hc hX
      exact ⟨w, hwF, hw⟩
    have e : pick (orbit F X) = hex.choose := dite_eq_left hex
    rw [e]
    exact hex.choose_spec
  let σ : G ⧸ centralizer ({z} : Set G) → G ⧸ centralizer ({z} : Set G) := fun X =>
    pick (orbit F X) • X
  have horbσ : ∀ X, X ≠ H₀ → orbit F (σ X) = orbit F X := by
    intro X hX
    have : σ X = (⟨pick (orbit F X), (hpick X hX).1⟩ : F) • X := rfl
    rw [this, orbit_smul]
  have hS' : Even (S.erase H₀).card := by
    refine even_card_of_involution σ (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_)
    · obtain ⟨hne, hXS⟩ := Finset.mem_erase.mp hX
      rw [hSdef, Finset.mem_filter] at hXS
      obtain ⟨-, haX, hτX⟩ := hXS
      obtain ⟨hwF, hw⟩ := hpick X hne
      obtain ⟨h4, h5⟩ := (hw X (mem_orbit_self X)).2.2 haX
      refine Finset.mem_erase.mpr ⟨fun h0 => hne ?_, ?_⟩
      · have : X = (pick (orbit F X))⁻¹ • σ X := (inv_smul_smul _ X).symm
        rw [this, h0, hH₀def, smul_one_coset (hFH (inv_mem hwF))]
      · rw [hSdef, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, h4, by rw [h5]; exact hτX⟩
    · obtain ⟨hne, -⟩ := Finset.mem_erase.mp hX
      change pick (orbit F (σ X)) • σ X = X
      rw [horbσ X hne]
      exact ((hpick X hne).2 X (mem_orbit_self X)).1
    · obtain ⟨hne, -⟩ := Finset.mem_erase.mp hX
      exact ((hpick X hne).2 X (mem_orbit_self X)).2.1
  rw [← Finset.card_erase_add_one hH₀] at hS
  exact (Nat.even_add_one.mp hS) hS'

end Smith

end CFSG.RankThree.Literature.FSmith
