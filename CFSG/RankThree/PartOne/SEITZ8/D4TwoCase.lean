module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Ring
public import CFSG.RankThree.PartOne.SEITZ8.D4TwoSeven

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.CTP
open scoped commutatorElement Matrix

variable {K : Type} [Field K] {σ : K →+* K} [CharP K 2]

omit [CharP K 2] in
theorem reflect_W_xH_check :
    reflect d4 (nd 3) (d4Root 22) = d4Root 22 ∧ reflect d4 (nd 1) (d4Root 22) = d4Root 22 ∧
    reflect d4 (nd 0) (d4Root 22) = d4Root 22 ∧ reflect d4 (nd 2) (d4Root 22) = d4Root 19 := by
  decide +kernel

theorem Wt_xH (c : K) : Wt * xd 22 c * Wt⁻¹ = xd 19 c := by
  obtain ⟨h1, h2, h3, h4⟩ := reflect_W_xH_check
  have e : Wt * xd 22 c * Wt⁻¹ = weylElement d4 K (nd 2) * (weylElement d4 K (nd 0) *
      (weylElement d4 K (nd 1) * (weylElement d4 K (nd 3) * xd 22 c *
        (weylElement d4 K (nd 3))⁻¹) * (weylElement d4 K (nd 1))⁻¹) *
          (weylElement d4 K (nd 0))⁻¹) * (weylElement d4 K (nd 2))⁻¹ := by
    unfold Wt; group
  rw [e, weylElement_conj_xd (nd 3) (by norm_num) h1, weylElement_conj_xd (nd 1) (by norm_num) h2,
    weylElement_conj_xd (nd 0) (by norm_num) h3, weylElement_conj_xd (nd 2) (by norm_num) h4]

omit [CharP K 2] in
theorem reflect_W_xAB_check :
    reflect d4 (nd 3) (d4Root 5) = d4Root 13 ∧ reflect d4 (nd 1) (d4Root 13) = d4Root 19 ∧
    reflect d4 (nd 0) (d4Root 19) = d4Root 15 ∧ reflect d4 (nd 2) (d4Root 15) = d4Root 15 ∧
    reflect d4 (nd 3) (d4Root 7) = d4Root 15 ∧ reflect d4 (nd 1) (d4Root 15) = d4Root 9 ∧
    reflect d4 (nd 0) (d4Root 9) = d4Root 13 ∧ reflect d4 (nd 2) (d4Root 13) = d4Root 13 ∧
    reflect d4 (nd 3) (d4Root 9) = d4Root 2 ∧ reflect d4 (nd 1) (d4Root 2) = d4Root 7 ∧
    reflect d4 (nd 0) (d4Root 7) = d4Root 12 ∧ reflect d4 (nd 2) (d4Root 12) = d4Root 12 := by
  decide +kernel

theorem Wt_conj_gen {p q1 q2 q3 q : ℕ} (hp : p < 24) (hq1 : q1 < 24) (hq2 : q2 < 24)
    (hq3 : q3 < 24) (h3 : reflect d4 (nd 3) (d4Root p) = d4Root q1)
    (h1 : reflect d4 (nd 1) (d4Root q1) = d4Root q2)
    (h0 : reflect d4 (nd 0) (d4Root q2) = d4Root q3)
    (h2 : reflect d4 (nd 2) (d4Root q3) = d4Root q) (c : K) :
    Wt * xd p c * Wt⁻¹ = xd q c := by
  have e : Wt * xd p c * Wt⁻¹ = weylElement d4 K (nd 2) * (weylElement d4 K (nd 0) *
      (weylElement d4 K (nd 1) * (weylElement d4 K (nd 3) * xd p c *
        (weylElement d4 K (nd 3))⁻¹) * (weylElement d4 K (nd 1))⁻¹) *
          (weylElement d4 K (nd 0))⁻¹) * (weylElement d4 K (nd 2))⁻¹ := by
    unfold Wt; group
  rw [e, weylElement_conj_xd (nd 3) hp h3, weylElement_conj_xd (nd 1) hq1 h1,
    weylElement_conj_xd (nd 0) hq2 h0, weylElement_conj_xd (nd 2) hq3 h2]

theorem Wt_xAB (hσ : ∀ c, σ (σ (σ c)) = c) (c : K) :
    Wt * xAB σ c * Wt⁻¹ = xAAB σ (σ (σ c)) := by
  obtain ⟨a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4⟩ := reflect_W_xAB_check
  unfold xAB xAAB
  rw [conj_mul_eq, conj_mul_eq, Wt_conj_gen (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) a1 a2 a3 a4, Wt_conj_gen (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) b1 b2 b3 b4, Wt_conj_gen (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c1 c2 c3 c4]
  simp only [hσ]
  d4coll

theorem conj_xAAB (c : ℕ → K) (hc1 : c 1 = 0) (r : K) :
    ordT σ c * xAAB σ r * (ordT σ c)⁻¹ =
      xAAB σ r * xH (c 4 * σ r + σ (c 4) * σ (σ r) + σ (σ (c 4)) * r) := by
  unfold ordT xA xAB xAAB xB xN xH
  rw [hc1]
  simp only [mul_inv_rev, xd_inv, map_zero, xd_zero, mul_one]
  d4coll
  d4fin

structure RatH (σ : K →+* K) (k : Subfield K) (H : Subgroup (adjointGroup d4 K)) : Prop where
  A : ∀ a ∈ k, xA σ a ∈ H
  x2 : xB (1 : K) ∈ H
  y2 : xd 8 (1 : K) ∈ H
  n0 : nB K ∈ H
  n1 : weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) ∈ H

section Rat

variable {k : Subfield K} {H : Subgroup (adjointGroup d4 K)} (hH : RatH σ k H)
include hH

omit [CharP K 2] in
theorem RatH.Wt_mem : (Wt : adjointGroup d4 K) ∈ H := mul_mem hH.n0 hH.n1

theorem RatH.xAB_mem {a : K} (ha : a ∈ k) : xAB σ a ∈ H := by
  have := H.mul_mem (H.mul_mem hH.n0 (hH.A a ha)) (H.inv_mem hH.n0)
  rwa [nB_xA] at this

theorem RatH.xAAB_mem (hσ : ∀ c, σ (σ (σ c)) = c) (hkσ : ∀ a ∈ k, σ a ∈ k) {a : K} (ha : a ∈ k) :
    xAAB σ a ∈ H := by
  have h := H.mul_mem (H.mul_mem hH.Wt_mem (hH.xAB_mem (hkσ a ha))) (H.inv_mem hH.Wt_mem)
  rwa [Wt_xAB hσ, hσ] at h

theorem RatH.xH_one_mem : xH (1 : K) ∈ H := by
  have e : Wt * xB (1 : K) * Wt⁻¹ = xH 1 := Wt_xB 1
  have := H.mul_mem (H.mul_mem hH.Wt_mem hH.x2) (H.inv_mem hH.Wt_mem)
  rwa [e] at this

theorem RatH.xN_one_mem : xN (1 : K) ∈ H := by
  have e : Wt * xH (1 : K) * Wt⁻¹ = xN 1 := Wt_xH 1
  have := H.mul_mem (H.mul_mem hH.Wt_mem hH.xH_one_mem) (H.inv_mem hH.Wt_mem)
  rwa [e] at this

end Rat

@[expose] def tf (σ : K →+* K) (a r : K) : K := a * σ r + σ a * σ (σ r) + σ (σ a) * r

omit [CharP K 2] in
theorem tf_fixed (hσ : ∀ c, σ (σ (σ c)) = c) (a r : K) : σ (tf σ a r) = tf σ a r := by
  unfold tf
  simp only [map_add, map_mul, hσ]
  ring

theorem ordT_commute_xH (c : ℕ → K) (d : K) : Commute (ordT σ c) (xH d) := by
  unfold ordT
  exact (((((commute_xB_xH _ d).mul_left (commute_xA_xH _ d)).mul_left
    (commute_xAB_xH _ d)).mul_left (commute_xAAB_xH _ d)).mul_left
    (commute_xH_xN d _).symm).mul_left (commute_xd_same 22 _ d)

theorem Wt_xB' (c : K) : Wt * xB c * Wt⁻¹ = xH c := Wt_xB c

theorem Wt_xH' (c : K) : Wt * xH c * Wt⁻¹ = xN c := Wt_xH c

theorem xH_mul_self (c : K) : xH c * xH c = 1 := xd_mul_self 22 c

section Gens

variable {k : Subfield K} {H : Subgroup (adjointGroup d4 K)} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem comap_le_of_gens (hkσ : ∀ a ∈ k, σ a ∈ k) (hH : RatH σ k H) {c : ℕ → K} (hc1 : c 1 = 0)
    (hc0 : σ (c 0) = c 0) {μ : K} (hμσ : σ μ = μ)
    (hy : ordT σ c * xd 23 μ * (ordT σ c)⁻¹ ∈ H) :
    Gam σ k (fun κ => ⟨tf σ (c 4) (σ (σ κ)), tf_fixed hσ _ _⟩) ⟨c 0, hc0⟩ ⟨μ, hμσ⟩ ≤
      H.comap (MulAut.conj (ordT σ c * Wt)).toMonoidHom := by
  have hconj : ∀ g : adjointGroup d4 K, (ordT σ c * Wt) * g * (ordT σ c * Wt)⁻¹ =
      ordT σ c * (Wt * g * Wt⁻¹) * (ordT σ c)⁻¹ := fun g => by group
  have hcomm : ∀ d : K, ordT σ c * xH d * (ordT σ c)⁻¹ = xH d := fun d => by
    rw [(ordT_commute_xH c d).eq]
    group
  refine (Subgroup.closure_le _).2 ?_
  rintro g (hg | ⟨κ, hκ, rfl⟩)
  · rcases hg with rfl | rfl | rfl
    · show (ordT σ c * Wt) * xB 1 * (ordT σ c * Wt)⁻¹ ∈ H
      rw [hconj, Wt_xB', hcomm]
      exact hH.xH_one_mem
    · show (ordT σ c * Wt) * xd 8 μ * (ordT σ c * Wt)⁻¹ ∈ H
      rw [hconj, Wt_xBneg]
      exact hy
    · show (ordT σ c * Wt) * (xH 1 * xB (c 0)) * (ordT σ c * Wt)⁻¹ ∈ H
      rw [conj_mul_eq, hconj, hconj, Wt_xH', Wt_xB', hcomm, conj_xN σ c, mul_assoc, mul_one,
        xH_mul_self, mul_one]
      exact hH.xN_one_mem
  · show (ordT σ c * Wt) * (xAB σ κ * xB (tf σ (c 4) (σ (σ κ)))) * (ordT σ c * Wt)⁻¹ ∈ H
    rw [conj_mul_eq, hconj, hconj, Wt_xAB hσ, Wt_xB', hcomm, conj_xAAB c hc1, mul_assoc]
    simp only [tf]
    rw [xH_mul_self, mul_one]
    exact hH.xAAB_mem hσ hkσ (hkσ _ (hkσ _ hκ))

end Gens

section KappaIrr

variable {k : Subfield K} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

omit [CharP K 2] in
theorem tf_swap (a b : K) : tf σ a b = tf σ b (σ a) := by
  unfold tf
  simp only [hσ]
  ring

omit [CharP K 2] hσ in
theorem tf_add_left (a a' b : K) : tf σ (a + a') b = tf σ a b + tf σ a' b := by
  unfold tf
  simp only [map_add]
  ring

omit [CharP K 2] hσ in
theorem tf_apply (δ : K →+* K) (hcomm : ∀ c, δ (σ c) = σ (δ c)) (a b : K) :
    δ (tf σ a b) = tf σ (δ a) (δ b) := by
  unfold tf
  simp only [map_add, map_mul, hcomm]

theorem exists_kappa_irr (hne : ∃ a, σ a ≠ a)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a})
    (δ : K →+* K) (hcomm : ∀ c, δ (σ c) = σ (δ c)) (hfix : ∀ c ∈ k, δ c = c)
    (hkδ : ∀ c, δ c = c → c ∈ k) {d : K} (hd : d ∉ k) : ∃ κ ∈ k, tf σ d κ ∉ k := by
  by_contra hcon
  push Not at hcon
  have hz : δ d + d ≠ 0 := by
    intro h
    apply hd
    apply hkδ
    have := congrArg (· + d) h
    simpa [add_assoc, CharTwo.add_self_eq_zero] using this
  have key : ∀ κ ∈ k, tf σ κ (σ (δ d + d)) = 0 := by
    intro κ hκ
    have h1 : tf σ (δ d) κ = tf σ d κ := by
      have := tf_apply δ hcomm d κ
      rw [hfix κ hκ, hfix _ (hcon κ hκ)] at this
      exact this.symm
    rw [← tf_swap hσ, tf_add_left, h1, CharTwo.add_self_eq_zero]
  obtain ⟨κ, hκ, hne0⟩ := exists_kappa hσ hne hspan ((map_ne_zero σ).2 hz)
  exact hne0 (key κ hκ)

end KappaIrr

section CaseA

variable {k : Subfield K} {H : Subgroup (adjointGroup d4 K)} [Finite K]
  (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

omit [Finite K] hσ in
theorem dv_inv_self (x y : fixedField σ) : (dv x y : adjointGroup d4 K)⁻¹ = dv x y :=
  inv_eq_of_mul_eq_one_right (by
    rw [dv_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, dv_zero])

omit hσ [Finite K] [CharP K 2] in
theorem dv_zero_left (b : fixedField σ) : (dv 0 b : adjointGroup d4 K) = xN (b : K) := by
  simp [dv, xH, xN, xd_zero]

theorem caseA_full_three (hne : ∃ a, σ a ≠ a)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a})
    (δ : K →+* K) (hcomm : ∀ c, δ (σ c) = σ (δ c)) (hfix : ∀ c ∈ k, δ c = c)
    (hkδ : ∀ c, δ c = c → c ∈ k) {k₂ : Subfield (fixedField σ)} (hk₂ : Nat.card k₂ = 2)
    (hk₂mem : ∀ c : fixedField σ, c ∈ k₂ ↔ (c : K) ∈ k) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hF : Nat.card (fixedField σ) = Nat.card k₂ ^ d) (hH : RatH σ k H)
    {c : ℕ → K} (hc1 : c 1 = 0) (hc0 : σ (c 0) = c 0) {μ : K} (hμσ : σ μ = μ) (hμ : μ ≠ 0)
    (hy : ordT σ c * xd 23 μ * (ordT σ c)⁻¹ ∈ H) (hirr : ¬ (c 0 ∈ k ∧ c 4 ∈ k)) :
    ∀ a : fixedField σ, xN (a : K) ∈ H := by
  have hkσ : ∀ a ∈ k, σ a ∈ k := fun a ha => hkδ _ (by rw [hcomm, hfix a ha])
  have hle := comap_le_of_gens hσ hkσ hH hc1 hc0 hμσ hy
  have hirr' : ¬ ((⟨c 0, hc0⟩ : fixedField σ) ∈ k₂ ∧ ∀ κ ∈ k,
      (⟨tf σ (c 4) (σ (σ κ)), tf_fixed hσ _ _⟩ : fixedField σ) ∈ k₂) := by
    rintro ⟨h0, h4⟩
    apply hirr
    refine ⟨(hk₂mem _).1 h0, ?_⟩
    by_contra h4k
    obtain ⟨κ, hκ, hκn⟩ := exists_kappa_irr hσ hne hspan δ hcomm hfix hkδ h4k
    apply hκn
    have := (hk₂mem _).1 (h4 (σ κ) (hkσ κ hκ))
    simpa [hσ] using this
  have hμ' : (⟨μ, hμσ⟩ : fixedField σ) ≠ 0 := fun h => hμ (congrArg Subtype.val h)
  have hgam := gamma_full hσ hne hspan hk₂ hd hd2 hF hμ' hirr'
  set t : fixedField σ := ⟨c 0, hc0⟩ with ht
  have hL : ∀ a : fixedField σ, dv (t * a) a ∈ H := by
    intro a
    have h' : (ordT σ c * Wt) * xH (a : K) * (ordT σ c * Wt)⁻¹ ∈ H := hle (hgam a)
    rw [show (ordT σ c * Wt) * xH (a : K) * (ordT σ c * Wt)⁻¹ =
      ordT σ c * (Wt * xH (a : K) * Wt⁻¹) * (ordT σ c)⁻¹ by group, Wt_xH', conj_xN σ c] at h'
    have e : dv (t * a) a = xN (a : K) * xH (c 0 * a) := by
      unfold dv
      exact (commute_xH_xN _ _).eq
    rw [e]
    exact h'
  have h8 : xd 8 (((1 : fixedField σ) : K)) ∈ H := hH.y2
  have hx3 : ∀ a : fixedField σ, xN ((t * a : fixedField σ) : K) ∈ H := by
    intro a
    have e2 := H.mul_mem (H.mul_mem h8 (hL a)) (H.inv_mem h8)
    rw [x8_conj_dv] at e2
    have e3 := H.mul_mem (H.inv_mem (hL a)) e2
    rw [dv_inv_self, dv_mul, CharTwo.add_self_eq_zero, dv_zero_left] at e3
    have hab : ∀ x y : K, x + (x + y) = y := fun x y => by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    simpa [hab] using e3
  intro u
  by_cases h0 : t = 0
  · have := hL u
    rwa [h0, zero_mul, dv_zero_left] at this
  · have := hx3 (u / t)
    rwa [mul_div_cancel₀ u h0] at this

end CaseA

variable (K) in
@[expose] noncomputable def nW1 : adjointGroup d4 K :=
  weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3)

omit [CharP K 2] in
theorem reflect_n1_check :
    (reflect d4 (nd 3) (d4Root 2) = d4Root 9 ∧ reflect d4 (nd 1) (d4Root 9) = d4Root 15 ∧
      reflect d4 (nd 0) (d4Root 15) = d4Root 19) ∧
    (reflect d4 (nd 3) (d4Root 5) = d4Root 13 ∧ reflect d4 (nd 1) (d4Root 13) = d4Root 19 ∧
      reflect d4 (nd 0) (d4Root 19) = d4Root 15) ∧
    (reflect d4 (nd 3) (d4Root 7) = d4Root 15 ∧ reflect d4 (nd 1) (d4Root 15) = d4Root 9 ∧
      reflect d4 (nd 0) (d4Root 9) = d4Root 13) ∧
    (reflect d4 (nd 3) (d4Root 9) = d4Root 2 ∧ reflect d4 (nd 1) (d4Root 2) = d4Root 7 ∧
      reflect d4 (nd 0) (d4Root 7) = d4Root 12) ∧
    (reflect d4 (nd 3) (d4Root 12) = d4Root 19 ∧ reflect d4 (nd 1) (d4Root 19) = d4Root 13 ∧
      reflect d4 (nd 0) (d4Root 13) = d4Root 9) ∧
    (reflect d4 (nd 3) (d4Root 15) = d4Root 7 ∧ reflect d4 (nd 1) (d4Root 7) = d4Root 2 ∧
      reflect d4 (nd 0) (d4Root 2) = d4Root 5) ∧
    (reflect d4 (nd 3) (d4Root 13) = d4Root 5 ∧ reflect d4 (nd 1) (d4Root 5) = d4Root 12 ∧
      reflect d4 (nd 0) (d4Root 12) = d4Root 7) ∧
    (reflect d4 (nd 3) (d4Root 19) = d4Root 12 ∧ reflect d4 (nd 1) (d4Root 12) = d4Root 5 ∧
      reflect d4 (nd 0) (d4Root 5) = d4Root 2) ∧
    (reflect d4 (nd 3) (d4Root 22) = d4Root 22 ∧ reflect d4 (nd 1) (d4Root 22) = d4Root 22 ∧
      reflect d4 (nd 0) (d4Root 22) = d4Root 22) := by
  decide +kernel

theorem N1_conj_gen {p q1 q2 q : ℕ} (hp : p < 24) (hq1 : q1 < 24) (hq2 : q2 < 24)
    (h3 : reflect d4 (nd 3) (d4Root p) = d4Root q1)
    (h1 : reflect d4 (nd 1) (d4Root q1) = d4Root q2)
    (h0 : reflect d4 (nd 0) (d4Root q2) = d4Root q) (c : K) :
    nW1 K * xd p c * (nW1 K)⁻¹ = xd q c := by
  have e : nW1 K * xd p c * (nW1 K)⁻¹ = weylElement d4 K (nd 0) * (weylElement d4 K (nd 1) *
      (weylElement d4 K (nd 3) * xd p c * (weylElement d4 K (nd 3))⁻¹) *
        (weylElement d4 K (nd 1))⁻¹) * (weylElement d4 K (nd 0))⁻¹ := by
    unfold nW1; group
  rw [e, weylElement_conj_xd (nd 3) hp h3, weylElement_conj_xd (nd 1) hq1 h1,
    weylElement_conj_xd (nd 0) hq2 h0]

theorem n1_conj_ordT (hσ : ∀ c, σ (σ (σ c)) = c) (c : ℕ → K) (hc1 : c 1 = 0) :
    nW1 K * ordT σ c * (nW1 K)⁻¹ =
      ordT σ (mkT (c 3) 0 (σ (c 8)) (σ (σ (c 4))) (c 0)
        (c 7 + c 0 * c 3 + tf σ (σ (c 8)) (σ (σ (c 4))))) := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1', c2, c3⟩, ⟨d1, d2, d3⟩, ⟨e1, e2, e3⟩, ⟨f1, f2, f3⟩,
    ⟨g1, g2, g3⟩, ⟨h1, h2, h3⟩, ⟨i1, i2, i3⟩⟩ := reflect_n1_check
  rw [ordT_zero_one]
  have hL : ordT σ c = xd 2 (c 0) * (xd 5 (c 4) * xd 7 (σ (c 4)) * xd 9 (σ (σ (c 4)))) *
      (xd 12 (c 8) * xd 15 (σ (c 8)) * xd 13 (σ (σ (c 8)))) * xd 19 (c 3) * xd 22 (c 7) := by
    unfold ordT xB xA xAB xAAB xN xH
    rw [hc1]
    simp only [map_zero, xd_zero, mul_one]
  rw [hL]
  simp only [conj_mul_eq,
    N1_conj_gen (p := 2) (by norm_num) (by norm_num) (by norm_num) a1 a2 a3,
    N1_conj_gen (p := 5) (by norm_num) (by norm_num) (by norm_num) b1 b2 b3,
    N1_conj_gen (p := 7) (by norm_num) (by norm_num) (by norm_num) c1' c2 c3,
    N1_conj_gen (p := 9) (by norm_num) (by norm_num) (by norm_num) d1 d2 d3,
    N1_conj_gen (p := 12) (by norm_num) (by norm_num) (by norm_num) e1 e2 e3,
    N1_conj_gen (p := 15) (by norm_num) (by norm_num) (by norm_num) f1 f2 f3,
    N1_conj_gen (p := 13) (by norm_num) (by norm_num) (by norm_num) g1 g2 g3,
    N1_conj_gen (p := 19) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3,
    N1_conj_gen (p := 22) (by norm_num) (by norm_num) (by norm_num) i1 i2 i3]
  unfold xB xAB xAAB xN xH tf
  simp only [hσ]
  d4coll
  ring_nf

omit [CharP K 2] in
theorem repCheck_21_22 : RootOps.repCheck d4 21 22 [(1, 1, 2, 1)] = true ∨
    RootOps.repCheck d4 21 22 [(1, 1, 2, -1)] = true := by
  first | exact Or.inl (by decide +kernel) | exact Or.inr (by decide +kernel)

omit [CharP K 2] in
theorem repCheck_8_21 : RootOps.repCheck d4 8 21 [(1, 1, 23, 1)] = true ∨
    RootOps.repCheck d4 8 21 [(1, 1, 23, -1)] = true := by
  first | exact Or.inl (by decide +kernel) | exact Or.inr (by decide +kernel)

theorem swap_21_22 (x y : K) :
    xd 21 y * xd 22 x = xd 2 (x * y) * (xd 22 x * xd 21 y) := by
  rcases repCheck_21_22 with h | h
  · exact swap_gen (Or.inl rfl) h x y
  · exact swap_gen (Or.inr rfl) h x y

theorem swap_8_21 (x y : K) :
    xd 8 y * xd 21 x = xd 23 (x * y) * (xd 21 x * xd 8 y) := by
  rcases repCheck_8_21 with h | h
  · exact swap_gen (Or.inl rfl) h x y
  · exact swap_gen (Or.inr rfl) h x y

omit [CharP K 2] in
theorem repCheck_21_23 : RootOps.repCheck d4 21 23 [] = true := by decide +kernel

theorem commute_21_23 (x y : K) : Commute (xd 21 x) (xd 23 y) :=
  commute_gen repCheck_21_23 x y

theorem x21_conj_xH (c : K) : xd 21 1 * xd 22 c * (xd 21 1)⁻¹ = xd 2 c * xd 22 c := by
  rw [xd_inv, swap_21_22]
  simp only [mul_one, mul_assoc, xd_mul_self, mul_one]

section Moves

variable {H : Subgroup (adjointGroup d4 K)}

theorem mem_of_conj_nB (hn : nB K ∈ H) {p q : ℕ} (hp : p < 24)
    (h : reflect d4 (nd 2) (d4Root p) = d4Root q) {c : K} (hc : xd p c ∈ H) : xd q c ∈ H := by
  have := H.mul_mem (H.mul_mem hn hc) (H.inv_mem hn)
  rwa [nB_xd hp h] at this

theorem mem_of_conj_nW1 (hn : nW1 K ∈ H) {p q1 q2 q : ℕ} (hp : p < 24) (hq1 : q1 < 24)
    (hq2 : q2 < 24) (h3 : reflect d4 (nd 3) (d4Root p) = d4Root q1)
    (h1 : reflect d4 (nd 1) (d4Root q1) = d4Root q2)
    (h0 : reflect d4 (nd 0) (d4Root q2) = d4Root q) {c : K} (hc : xd p c ∈ H) : xd q c ∈ H := by
  have := H.mul_mem (H.mul_mem hn hc) (H.inv_mem hn)
  rwa [N1_conj_gen hp hq1 hq2 h3 h1 h0] at this

omit [CharP K 2] in
theorem reflect_moves_check :
    reflect d4 (nd 2) (d4Root 23) = d4Root 21 ∧ reflect d4 (nd 2) (d4Root 8) = d4Root 2 ∧
    reflect d4 (nd 2) (d4Root 19) = d4Root 22 ∧
    ∃ q1 < 24, ∃ q2 < 24, reflect d4 (nd 3) (d4Root 21) = d4Root q1 ∧
      reflect d4 (nd 1) (d4Root q1) = d4Root q2 ∧ reflect d4 (nd 0) (d4Root q2) = d4Root 8 := by
  decide +kernel

theorem x21_to_x8 (hn : nW1 K ∈ H) {c : K} (hc : xd 21 c ∈ H) : xd 8 c ∈ H := by
  obtain ⟨-, -, -, q1, hq1, q2, hq2, h3, h1, h0⟩ := reflect_moves_check
  exact mem_of_conj_nW1 hn (by norm_num) hq1 hq2 h3 h1 h0 hc

theorem x23_to_x22 (hn0 : nB K ∈ H) (hn1 : nW1 K ∈ H) {c : K} (hc : xd 23 c ∈ H) :
    xd 22 c ∈ H := by
  obtain ⟨h23, h8, h19, -⟩ := reflect_moves_check
  obtain ⟨⟨a1, a2, a3⟩, -⟩ := reflect_n1_check
  have h21 := mem_of_conj_nB hn0 (by norm_num) h23 hc
  have h8' := x21_to_x8 hn1 h21
  have h2 := mem_of_conj_nB hn0 (by norm_num) h8 h8'
  have h19' := mem_of_conj_nW1 hn1 (by norm_num) (by norm_num) (by norm_num) a1 a2 a3 h2
  exact mem_of_conj_nB hn0 (by norm_num) h19 h19'

theorem RatH.x23_one_mem {k : Subfield K} (hH : RatH σ k H) : xd 23 (1 : K) ∈ H := by
  have := H.mul_mem (H.mul_mem hH.Wt_mem hH.y2) (H.inv_mem hH.Wt_mem)
  rwa [Wt_xBneg] at this

theorem RatH.x21_one_mem {k : Subfield K} (hH : RatH σ k H) : xd 21 (1 : K) ∈ H :=
  mem_of_conj_nB hH.n0 (by norm_num) reflect_moves_check.1 hH.x23_one_mem

theorem comm_x8_x21 (s t : K) : xd 8 s * xd 21 t * (xd 8 s)⁻¹ * (xd 21 t)⁻¹ = xd 23 (t * s) := by
  rw [swap_8_21]
  group

theorem full_x23_of_irrational [Finite K] {k : Subfield K} (hH : RatH σ k H)
    {k₂ : Subfield (fixedField σ)} (hk₂ : Nat.card k₂ = 2) {d : ℕ} (hd : d.Prime)
    (hF : Nat.card (fixedField σ) = Nat.card k₂ ^ d) {μ : K} (hμσ : σ μ = μ) (hμk : μ ∉ k)
    (hμ : xd 23 μ ∈ H) : ∀ t : fixedField σ, xd 23 (t : K) ∈ H := by
  have h21 : ∀ t : K, xd 23 t ∈ H → xd 21 t ∈ H := fun t h =>
    mem_of_conj_nB hH.n0 (by norm_num) reflect_moves_check.1 h
  have h8 : ∀ t : K, xd 23 t ∈ H → xd 8 t ∈ H := fun t h => x21_to_x8 hH.n1 (h21 t h)
  let T : Subring (fixedField σ) :=
    { carrier := {t | xd 23 (t : K) ∈ H}
      mul_mem' := fun {s t} hs ht => by
        have hs8 := h8 _ hs
        have ht21 := h21 _ ht
        have hc := H.mul_mem (H.mul_mem (H.mul_mem hs8 ht21) (H.inv_mem hs8)) (H.inv_mem ht21)
        rw [comm_x8_x21] at hc
        show xd 23 ((s * t : fixedField σ) : K) ∈ H
        rw [show ((s * t : fixedField σ) : K) = (t : K) * s by
          show (s : K) * t = t * s
          ring]
        exact hc
      one_mem' := hH.x23_one_mem
      add_mem' := fun {s t} hs ht => by
        show xd 23 (((s + t : fixedField σ)) : K) ∈ H
        rw [show (((s + t : fixedField σ)) : K) = (s : K) + t from rfl, xd_add]
        exact H.mul_mem hs ht
      zero_mem' := by
        show xd 23 (((0 : fixedField σ)) : K) ∈ H
        rw [show (((0 : fixedField σ)) : K) = 0 from rfl, xd_zero]
        exact H.one_mem
      neg_mem' := fun {s} hs => by
        show xd 23 (((-s : fixedField σ)) : K) ∈ H
        rw [show (((-s : fixedField σ)) : K) = -(s : K) from rfl, CharTwo.neg_eq]
        exact hs }
  have hKd : Nat.card (fixedField σ) = 2 ^ d := by rw [hF, hk₂]
  have hμ0 : (⟨μ, hμσ⟩ : fixedField σ) ≠ 0 := fun h => hμk (by
    have : μ = 0 := congrArg Subtype.val h
    rw [this]
    exact k.zero_mem)
  have hμ1 : (⟨μ, hμσ⟩ : fixedField σ) ≠ 1 := fun h => hμk (by
    have : μ = 1 := congrArg Subtype.val h
    rw [this]
    exact k.one_mem)
  have hT : T = ⊤ := SEITZ2.subring_eq_top_of_card_prime hd hKd T (a := ⟨μ, hμσ⟩) hμ hμ0 hμ1
  intro t
  have : t ∈ T := hT ▸ Subring.mem_top t
  exact this

end Moves

omit [CharP K 2] in
theorem reflect_n1_23_check :
    reflect d4 (nd 3) (d4Root 23) = d4Root 23 ∧ reflect d4 (nd 1) (d4Root 23) = d4Root 23 ∧
    reflect d4 (nd 0) (d4Root 23) = d4Root 23 := by
  decide +kernel

theorem nW1_xd23 (c : K) : nW1 K * xd 23 c * (nW1 K)⁻¹ = xd 23 c :=
  N1_conj_gen (by norm_num) (by norm_num) (by norm_num) reflect_n1_23_check.1
    reflect_n1_23_check.2.1 reflect_n1_23_check.2.2 c

section Cases

variable {k : Subfield K} {H : Subgroup (adjointGroup d4 K)} [Finite K]
  (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

omit [CharP K 2] [Finite K] hσ in
theorem eq_zero_or_one_of_mem {k₂ : Subfield (fixedField σ)} (hk₂ : Nat.card k₂ = 2)
    (hk₂mem : ∀ c : fixedField σ, c ∈ k₂ ↔ (c : K) ∈ k) {c : K} (hcσ : σ c = c) (hck : c ∈ k) :
    c = 0 ∨ c = 1 := by
  rcases eq_zero_or_one_of_card_two hk₂ ((hk₂mem ⟨c, hcσ⟩).2 hck) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem core_cases (hne : ∃ a, σ a ≠ a)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a})
    (δ : K →+* K) (hcomm : ∀ c, δ (σ c) = σ (δ c)) (hfix : ∀ c ∈ k, δ c = c)
    (hkδ : ∀ c, δ c = c → c ∈ k) {k₂ : Subfield (fixedField σ)} (hk₂ : Nat.card k₂ = 2)
    (hk₂mem : ∀ c : fixedField σ, c ∈ k₂ ↔ (c : K) ∈ k) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hF : Nat.card (fixedField σ) = Nat.card k₂ ^ d) (hH : RatH σ k H)
    {c : ℕ → K} (hc1 : c 1 = 0) (hc0 : σ (c 0) = c 0) (hc3 : σ (c 3) = c 3)
    (hc7 : σ (c 7) = c 7) {μ : K} (hμσ : σ μ = μ) (hμk : μ ∉ k)
    (hy : ordT σ c * xd 23 μ * (ordT σ c)⁻¹ ∈ H) : ∀ a : fixedField σ, xH (a : K) ∈ H := by
  have hμ0 : μ ≠ 0 := fun h => hμk (h ▸ k.zero_mem)
  have hkσ : ∀ a ∈ k, σ a ∈ k := fun a ha => hkδ _ (by rw [hcomm, hfix a ha])
  have hkσ' : ∀ a, σ a ∈ k → a ∈ k := fun a h => by
    have := hkσ _ (hkσ _ h)
    rwa [hσ] at this
  have fin3 : (∀ a : fixedField σ, xN (a : K) ∈ H) → ∀ a : fixedField σ, xH (a : K) ∈ H :=
    fun h3 a => by
      have := H.mul_mem (H.mul_mem hH.n0 (h3 a)) (H.inv_mem hH.n0)
      rwa [nB_xN] at this
  have caseA : ∀ {c' : ℕ → K}, c' 1 = 0 → σ (c' 0) = c' 0 →
      ordT σ c' * xd 23 μ * (ordT σ c')⁻¹ ∈ H → ¬ (c' 0 ∈ k ∧ c' 4 ∈ k) →
        ∀ a : fixedField σ, xH (a : K) ∈ H := fun hc1' hc0' hy' hirr =>
    fin3 (caseA_full_three hσ hne hspan δ hcomm hfix hkδ hk₂ hk₂mem hd hd2 hF hH hc1' hc0' hμσ
      hμ0 hy' hirr)
  by_cases hA : ¬ (c 0 ∈ k ∧ c 4 ∈ k)
  · exact caseA hc1 hc0 hy hA
  by_cases hA' : ¬ (c 3 ∈ k ∧ c 8 ∈ k)
  · set c'' : ℕ → K := mkT (c 3) 0 (σ (c 8)) (σ (σ (c 4))) (c 0)
      (c 7 + c 0 * c 3 + tf σ (σ (c 8)) (σ (σ (c 4)))) with hc''
    have e0 : c'' 0 = c 3 := by simp [hc'', mkT]
    have e1 : c'' 1 = 0 := by simp [hc'', mkT]
    have e4 : c'' 4 = σ (c 8) := by simp [hc'', mkT]
    have hy' : ordT σ c'' * xd 23 μ * (ordT σ c'')⁻¹ ∈ H := by
      have hn1 : nW1 K ∈ H := hH.n1
      have h := H.mul_mem (H.mul_mem hn1 hy) (H.inv_mem hn1)
      rwa [show nW1 K * (ordT σ c * xd 23 μ * (ordT σ c)⁻¹) * (nW1 K)⁻¹ =
          (nW1 K * ordT σ c * (nW1 K)⁻¹) * (nW1 K * xd 23 μ * (nW1 K)⁻¹) *
            (nW1 K * ordT σ c * (nW1 K)⁻¹)⁻¹ by group, n1_conj_ordT hσ c hc1, nW1_xd23] at h
    refine caseA e1 (by rw [e0]; exact hc3) hy' ?_
    rw [e0, e4]
    rintro ⟨h3k, h8k⟩
    exact hA' ⟨h3k, hkσ' _ h8k⟩
  push Not at hA hA'
  obtain ⟨hc0k, hc4k⟩ := hA
  obtain ⟨hc3k, hc8k⟩ := hA'
  have hx2 : ∀ e : K, σ e = e → e ∈ k → xB e ∈ H := fun e he hek => by
    rcases eq_zero_or_one_of_mem hk₂ hk₂mem he hek with rfl | rfl
    · simp only [xB, xd_zero]
      exact H.one_mem
    · exact hH.x2
  have hxN : ∀ e : K, σ e = e → e ∈ k → xN e ∈ H := fun e he hek => by
    rcases eq_zero_or_one_of_mem hk₂ hk₂mem he hek with rfl | rfl
    · simp only [xN, xd_zero]
      exact H.one_mem
    · exact hH.xN_one_mem
  have hxH : ∀ e : K, σ e = e → e ∈ k → xH e ∈ H := fun e he hek => by
    rcases eq_zero_or_one_of_mem hk₂ hk₂mem he hek with rfl | rfl
    · simp only [xH, xd_zero]
      exact H.one_mem
    · exact hH.xH_one_mem
  have hkσ'' : ∀ a ∈ k, σ a ∈ k := hkσ
  set q0 : adjointGroup d4 K := xB (c 0) * xAB σ (c 4) * xAAB σ (c 8) * xN (c 3) with hq0def
  have hq0 : q0 ∈ H := H.mul_mem (H.mul_mem (H.mul_mem (hx2 _ hc0 hc0k) (hH.xAB_mem hc4k))
    (hH.xAAB_mem hσ hkσ hc8k)) (hxN _ hc3 hc3k)
  have hP : ordT σ c = q0 * xH (c 7) := by
    unfold ordT xA
    rw [hc1]
    simp only [hq0def, map_zero, xd_zero, mul_one]
  have hy1 : xH (c 7) * xd 23 μ * (xH (c 7))⁻¹ ∈ H := by
    have h := H.mul_mem (H.mul_mem (H.inv_mem hq0) hy) hq0
    rwa [hP, show q0⁻¹ * (q0 * xH (c 7) * xd 23 μ * (q0 * xH (c 7))⁻¹) * q0 =
      xH (c 7) * xd 23 μ * (xH (c 7))⁻¹ by group] at h
  by_cases h7k : c 7 ∈ k
  · have h7 : xH (c 7) ∈ H := hxH _ hc7 h7k
    have h23 : xd 23 μ ∈ H := by
      have h := H.mul_mem (H.mul_mem (H.inv_mem h7) hy1) h7
      rwa [show (xH (c 7))⁻¹ * (xH (c 7) * xd 23 μ * (xH (c 7))⁻¹) * xH (c 7) = xd 23 μ by
        group] at h
    intro a
    exact x23_to_x22 hH.n0 hH.n1 (full_x23_of_irrational hH hk₂ hd hF hμσ hμk h23 a)
  · have h21 : xd 21 1 ∈ H := hH.x21_one_mem
    have hy2 := H.mul_mem (H.mul_mem h21 hy1) (H.inv_mem h21)
    have e : xd 21 1 * (xH (c 7) * xd 23 μ * (xH (c 7))⁻¹) * (xd 21 1)⁻¹ =
        ordT σ (mkT (c 7) 0 0 0 0 (c 7)) * xd 23 μ * (ordT σ (mkT (c 7) 0 0 0 0 (c 7)))⁻¹ := by
      rw [ordT_zero_one]
      simp only [xAB, xAAB, xN, map_zero, xd_zero, mul_one]
      rw [show xd 21 1 * (xH (c 7) * xd 23 μ * (xH (c 7))⁻¹) * (xd 21 1)⁻¹ =
        (xd 21 1 * xH (c 7) * (xd 21 1)⁻¹) * (xd 21 1 * xd 23 μ * (xd 21 1)⁻¹) *
          (xd 21 1 * xH (c 7) * (xd 21 1)⁻¹)⁻¹ by group]
      have e21 : xd 21 1 * xH (c 7) * (xd 21 1)⁻¹ = xB (c 7) * xH (c 7) := x21_conj_xH (c 7)
      have e23 : xd 21 1 * xd 23 μ * (xd 21 1)⁻¹ = xd 23 μ := by
        rw [(commute_21_23 1 μ).eq]
        group
      rw [e21, e23]
    rw [e] at hy2
    exact caseA (by simp [mkT]) (by simpa [mkT] using hc7) hy2 (by simpa [mkT] using h7k)

end Cases

end CFSG.RankThree.PartOne.SEITZ8
