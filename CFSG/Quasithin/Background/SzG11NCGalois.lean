module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.Quasithin.SzG11NC

open Polynomial

theorem zmod_two_add_self {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (v : V) :
    v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem smul_left_inj_of_ne_zero {E V : Type} [Field E] [AddCommGroup V] [Module E V] {v : V}
    (hv : v ≠ 0) {e e' : E} (h : e • v = e' • v) : e = e' := by
  by_contra hne
  apply hv
  have : (e - e') • v = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.1 this with h0 | h0
  · exact absurd (sub_eq_zero.1 h0) hne
  · exact h0

theorem eq_zero_or_one_of_smul_eq {E V : Type} [Field E] [AddCommGroup V] [Module E V] {v : V}
    (hv : v ≠ 0) {κ : E} (h : κ • v = 0 ∨ κ • v = v) : κ = 0 ∨ κ = 1 := by
  rcases h with h | h
  · left
    by_contra hne
    apply hv
    have := congrArg (fun w => κ⁻¹ • w) h
    simpa [smul_smul, inv_mul_cancel₀ hne] using this
  · right
    apply smul_left_inj_of_ne_zero hv
    rw [h, one_smul]

theorem exists_ne_zero_one {E : Type} [Field E] [Finite E] (hE : 2 < Nat.card E) :
    ∃ κ : E, κ ≠ 0 ∧ κ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set E) ⊆ {0, 1} := by
    intro κ _
    by_cases h : κ = 0
    · simp [h]
    · simp [hcon κ h]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair zero_ne_one, Set.ncard_univ] at this
  omega

@[expose] def toAlg {E : Type} [Field E] [Algebra (ZMod 2) E] (σ : E ≃+* E) : E ≃ₐ[ZMod 2] E :=
  AlgEquiv.ofRingEquiv (f := σ) (fun c => by
    have := RingHom.ext_zmod ((σ : E →+* E).comp (algebraMap (ZMod 2) E)) (algebraMap (ZMod 2) E)
    exact congrArg (fun f => f c) this)

theorem toAlg_apply {E : Type} [Field E] [Algebra (ZMod 2) E] (σ : E ≃+* E) (e : E) :
    toAlg σ e = σ e := rfl

theorem fix_ge_three {E : Type} [Field E] [Finite E] [CharP E 2] (hE : 8 ≤ Nat.card E)
    (σ : E ≃+* E) (hσ : ∀ x, σ (σ x) = x) : ∃ κ : E, κ ≠ 0 ∧ κ ≠ 1 ∧ σ κ = κ := by
  classical
  by_contra hcon
  push Not at hcon
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hN : ∀ x : E, x ≠ 0 → x * σ x = 1 := by
    intro x hx
    have hfix : σ (x * σ x) = x * σ x := by
      rw [map_mul, hσ, mul_comm]
    have h0 : x * σ x ≠ 0 := mul_ne_zero hx (by simpa using hx)
    by_cases h1 : x * σ x = 1
    · exact h1
    · exact absurd hfix (fun h => hcon _ h0 h1 h)
  have hroot : ∀ x : E, x ≠ 0 → x ≠ 1 → x ^ 2 + x + 1 = 0 := by
    intro x hx0 hx1
    have hx1' : x + 1 ≠ 0 := by
      intro h
      apply hx1
      linear_combination h - h2
    have e1 := hN x hx0
    have e2 := hN (x + 1) hx1'
    rw [map_add, map_one] at e2
    linear_combination x * e2 - (x + 1) * e1
  have : Fintype E := Fintype.ofFinite E
  let p : E[X] := X ^ 2 + X + 1
  have hp : p ≠ 0 := by
    intro h
    have := congrArg (fun q : E[X] => q.coeff 0) h
    simp [p] at this
  have hsub : (Finset.univ : Finset E) ⊆ {0, 1} ∪ p.roots.toFinset := by
    intro x _
    by_cases h0 : x = 0
    · simp [h0]
    by_cases h1 : x = 1
    · simp [h1]
    simp only [Finset.mem_union, Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
    right
    simpa [p] using hroot x h0 h1
  have hc := Finset.card_le_card hsub
  have hc2 := Finset.card_union_le ({0, 1} : Finset E) p.roots.toFinset
  have hc3 : p.roots.toFinset.card ≤ 2 := by
    calc p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := card_roots' p
      _ = 2 := by simp only [p]; compute_degree!
  have hc4 : ({0, 1} : Finset E).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
  omega

theorem exists_common_fix {E : Type} [Field E] [Finite E] [CharP E 2] (hE : 8 ≤ Nat.card E)
    (S : Set (E ≃+* E)) (hS : ∀ σ ∈ S, ∀ e, σ (σ e) = e) :
    ∃ κ : E, κ ≠ 0 ∧ κ ≠ 1 ∧ ∀ σ ∈ S, σ κ = κ := by
  classical
  let _ : Algebra (ZMod 2) E := ZMod.algebra E 2
  by_cases hid : ∀ σ ∈ S, ∀ e, σ e = e
  · obtain ⟨κ, h0, h1⟩ := exists_ne_zero_one (E := E) (by omega)
    exact ⟨κ, h0, h1, fun σ hσ => hid σ hσ κ⟩
  · push Not at hid
    obtain ⟨σ₀, hσ₀S, e₀, he₀⟩ := hid
    obtain ⟨κ, h0, h1, hfix⟩ := fix_ge_three hE σ₀ (hS σ₀ hσ₀S)
    refine ⟨κ, h0, h1, fun σ hσ => ?_⟩
    by_contra hσκ
    have : Fintype (E ≃ₐ[ZMod 2] E) := Fintype.ofFinite _
    have hsq : ∀ τ ∈ S, (toAlg τ) ^ 2 = 1 := by
      intro τ hτ
      apply AlgEquiv.ext
      intro e
      simp only [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply, toAlg_apply]
      exact hS τ hτ e
    have hcard := IsCyclic.card_pow_eq_one_le (α := E ≃ₐ[ZMod 2] E) (n := 2) (by norm_num)
    have hsub : ({1, toAlg σ₀, toAlg σ} : Finset (E ≃ₐ[ZMod 2] E)) ⊆
        Finset.univ.filter (fun a : E ≃ₐ[ZMod 2] E => a ^ 2 = 1) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl | rfl
      · simp
      · exact hsq σ₀ hσ₀S
      · exact hsq σ hσ
    have h10 : (1 : E ≃ₐ[ZMod 2] E) ≠ toAlg σ₀ := by
      intro h
      apply he₀
      have := congrArg (fun a : E ≃ₐ[ZMod 2] E => a e₀) h
      simpa [toAlg_apply] using this.symm
    have h1s : (1 : E ≃ₐ[ZMod 2] E) ≠ toAlg σ := by
      intro h
      apply hσκ
      have := congrArg (fun a : E ≃ₐ[ZMod 2] E => a κ) h
      simpa [toAlg_apply] using this.symm
    have h0s : toAlg σ₀ ≠ toAlg σ := by
      intro h
      apply hσκ
      have := congrArg (fun a : E ≃ₐ[ZMod 2] E => a κ) h
      simp only [toAlg_apply] at this
      rw [← this, hfix]
    have h3 : ({1, toAlg σ₀, toAlg σ} : Finset (E ≃ₐ[ZMod 2] E)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h10, h1s]),
        Finset.card_insert_of_notMem (by simp [h0s]), Finset.card_singleton]
    have := Finset.card_le_card hsub
    have hc' : (Finset.univ.filter (fun a : E ≃ₐ[ZMod 2] E => a ^ 2 = 1)).card ≤ 2 := hcard
    omega

theorem exists_theta {E : Type} [Field E] [CharP E 2] (σ : E ≃+* E) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ e, σ e ≠ e) : ∃ θ : E, θ + σ θ = 1 := by
  obtain ⟨t, ht⟩ := hne
  set c := t + σ t with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply ht
    have : σ t = - t := by linear_combination h
    rw [this, CharTwo.neg_eq]
  have hσc : σ c = c := by
    rw [hc, map_add, hσ, add_comm]
  refine ⟨t / c, ?_⟩
  rw [map_div₀, hσc, ← add_div, ← hc]
  exact div_self hc0

theorem E4_cases {E : Type} [Field E] [Finite E] (hE : Nat.card E = 4) (h2 : (2 : E) = 0) :
    ∃ ω : E, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 = ω + 1 ∧ ∀ e : E, e = 0 ∨ e = 1 ∨ e = ω ∨ e = ω + 1 := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = 4 := by rw [← Nat.card_eq_fintype_card]; exact hE
  have hlt : 2 < Nat.card E := by omega
  obtain ⟨ω, h0, h1⟩ := exists_ne_zero_one hlt
  have h3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω h0
    rwa [hcard] at this
  have hsq : ω ^ 2 = ω + 1 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h1
    · linear_combination h - h2 * (ω + 1)
  refine ⟨ω, h0, h1, hsq, fun e => ?_⟩
  have hne1 : ω + 1 ≠ 0 := by
    intro h
    apply h1
    linear_combination h - h2
  have hne2 : ω + 1 ≠ 1 := by
    intro h
    apply h0
    linear_combination h
  have hne3 : ω + 1 ≠ ω := by
    intro h
    have : (1 : E) = 0 := by linear_combination h
    exact one_ne_zero this
  have hS : ({0, 1, ω, ω + 1} : Finset E) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard]
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨zero_ne_one, h0.symm, hne1.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h1.symm, hne2.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact hne3.symm), Finset.card_singleton]
  have : e ∈ ({0, 1, ω, ω + 1} : Finset E) := by rw [hS]; exact Finset.mem_univ e
  simpa using this

end CFSG.Quasithin.SzG11NC
