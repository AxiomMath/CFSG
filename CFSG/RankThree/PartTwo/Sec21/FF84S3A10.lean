module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4UBasic
public import CFSG.RankThree.PartTwo.Sec21.FF84S4A8
public import CFSG.RankThree.PartTwo.Sec21.FF84S4BCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S4
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s m₁ m₂ Eo U₁ U₂ τ₀)

abbrev S5 := {x : Fin 8 // 3 ≤ x.val}

private def e5 : S5 ≃ Fin 5 where
  toFun x := ⟨x.1.val - 3, by have := x.1.isLt; omega⟩
  invFun i := ⟨⟨i.val + 3, by have := i.isLt; omega⟩, by simp⟩
  left_inv x := by
    apply Subtype.ext; apply Fin.ext
    have := x.2
    simp only
    omega
  right_inv i := by apply Fin.ext; simp

private def tf (σ : Perm S5) (i : Fin 5) : Fin 5 := e5 (σ (e5.symm i))

private theorem tf_mul (σ τ : Perm S5) (i : Fin 5) : tf (σ * τ) i = tf σ (tf τ i) := by
  simp [tf, Perm.mul_apply]

private theorem eq_one_iff_tf (σ : Perm S5) : σ = 1 ↔ ∀ i, tf σ i = i := by
  constructor
  · rintro rfl i; simp [tf]
  · intro h
    ext1 x
    have := h (e5 x)
    simp only [tf, Equiv.symm_apply_apply] at this
    simpa using congrArg e5.symm this

private theorem apply_eq_iff_tf (σ : Perm S5) (p : S5) : σ p = p ↔ tf σ (e5 p) = e5 p := by
  simp [tf]

private theorem tf_injective (σ : Perm S5) {i j : Fin 5} (h : tf σ i = tf σ j) : i = j := by
  simpa [tf] using h

private def signTab (g : Fin 5 → Fin 5) : ℤˣ :=
  ∏ x ∈ Equiv.Perm.finPairsLT 5, if g x.1 ≤ g x.2 then -1 else 1

private def signTabZ (g : Fin 5 → Fin 5) : ℤ :=
  ∏ x ∈ Equiv.Perm.finPairsLT 5, if g x.1 ≤ g x.2 then -1 else 1

private theorem signTab_coe (g : Fin 5 → Fin 5) : ((signTab g : ℤˣ) : ℤ) = signTabZ g := by
  simp only [signTab, signTabZ, Units.coe_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  split_ifs <;> simp

private theorem signAux3_eq_signAux {α : Type*} [DecidableEq α] [Finite α] {n : ℕ}
    (e : α ≃ Fin n) (f : Perm α) {s : Multiset α} (hs : ∀ x, x ∈ s) :
    Equiv.Perm.signAux3 f hs = Equiv.Perm.signAux ((e.symm.trans f).trans e) := by
  induction s using Quotient.inductionOn with
  | h l => exact (Equiv.Perm.signAux_eq_signAux2 l f e fun x _ => hs x).symm

private theorem sign_eq_signTab (σ : Perm S5) : sign σ = signTab (tf σ) :=
  signAux3_eq_signAux e5 σ (Finset.mem_univ)

private def mk5 (a b c d e : Fin 5) (i : Fin 5) : Fin 5 :=
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | _ => e

private def L16 : List (Fin 5 → Fin 5) :=
  [mk5 0 1 2 3 4, mk5 0 2 1 4 3, mk5 0 3 4 1 2, mk5 0 4 3 2 1,
    mk5 2 1 0 4 3, mk5 3 1 4 0 2, mk5 4 1 3 2 0, mk5 1 0 2 4 3,
    mk5 3 4 2 0 1, mk5 4 3 2 1 0, mk5 1 0 4 3 2, mk5 2 4 0 3 1,
    mk5 4 2 1 3 0, mk5 1 0 3 2 4, mk5 2 3 0 1 4, mk5 3 2 1 0 4]

set_option maxRecDepth 100000 in
private theorem even_pow8_tab : ∀ a : Fin 5, ∀ b : Fin 5, b ≠ a → ∀ c : Fin 5, c ≠ a → c ≠ b →
    ∀ d : Fin 5, d ≠ a → d ≠ b → d ≠ c → ∀ e : Fin 5, e ≠ a → e ≠ b → e ≠ c → e ≠ d →
    (∀ i, (mk5 a b c d e)^[8] i = i) →
    signTabZ (mk5 a b c d e) = 1 → ∃ k : Fin L16.length, ∀ i, mk5 a b c d e i = L16.get k i := by
  decide +kernel

private theorem tf_iterate (σ : Perm S5) (k : ℕ) (i : Fin 5) : (tf σ)^[k] i = tf (σ ^ k) i := by
  induction k with
  | zero => simp [tf]
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ', tf_mul]

private theorem even_pow8_mem (σ : Perm S5) (hs : sign σ = 1) (h8 : σ ^ 8 = 1) :
    ∃ t ∈ L16, ∀ i, tf σ i = t i := by
  have hne : ∀ {i j : Fin 5}, i ≠ j → tf σ i ≠ tf σ j := fun hij h => hij (tf_injective σ h)
  have heta : mk5 (tf σ 0) (tf σ 1) (tf σ 2) (tf σ 3) (tf σ 4) = tf σ := by
    funext i; fin_cases i <;> rfl
  have := even_pow8_tab (tf σ 0) (tf σ 1) (hne (by decide)) (tf σ 2) (hne (by decide))
    (hne (by decide)) (tf σ 3) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (tf σ 4) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
  rw [heta] at this
  obtain ⟨k, hk⟩ := this (fun i => by rw [tf_iterate, h8]; exact (eq_one_iff_tf 1).1 rfl i)
    (by rw [← signTab_coe, ← sign_eq_signTab, hs]; rfl)
  exact ⟨_, List.get_mem _ _, hk⟩

private theorem sq_pow8 {σ : Perm S5} (h : σ * σ = 1) : σ ^ 8 = 1 := by
  rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, sq, h, one_pow]

private theorem sq_iff_tab (σ : Perm S5) : σ * σ = 1 ↔ ∀ i, tf σ (tf σ i) = i := by
  rw [eq_one_iff_tf]; simp only [tf_mul]

set_option maxRecDepth 100000 in
private theorem L16_sq : ∀ t ∈ L16, ∀ i, t (t i) = i := by
  intro t ht
  obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
private theorem L16_D2 : ∀ t ∈ L16, ∀ u ∈ L16, ¬(∀ i, t i = i) → ¬(∀ i, u i = i) →
    (∀ i, t (u i) = u (t i)) → ∀ i, t i = i → u i = i := by
  intro t ht u hu
  obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
  obtain ⟨l, rfl⟩ := List.mem_iff_get.1 hu
  revert k l
  decide +kernel

set_option maxRecDepth 100000 in
private theorem L16_fix : ∀ t ∈ L16, ∃ i, t i = i := by
  intro t ht
  obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
private theorem L16_D4 : ∀ t ∈ L16, ¬(∀ i, t i = i) → ∀ i j, t i = i → t j = j → i = j := by
  intro t ht
  obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
  revert k
  decide +kernel

theorem D1 : ∀ σ : Perm S5, sign σ = 1 → σ ^ 8 = 1 → σ * σ = 1 := by
  intro σ hs h8
  obtain ⟨t, ht, hσ⟩ := even_pow8_mem σ hs h8
  rw [sq_iff_tab]; simp only [hσ]
  exact L16_sq t ht

theorem D2 : ∀ σ τ : Perm S5, sign σ = 1 → sign τ = 1 → σ * σ = 1 → τ * τ = 1 → σ ≠ 1 →
    τ ≠ 1 → σ * τ = τ * σ → ∀ p : S5, σ p = p → τ p = p := by
  intro σ τ hs ht hσ hτ h1 h1' hc p
  obtain ⟨t, htL, hσt⟩ := even_pow8_mem σ hs (sq_pow8 hσ)
  obtain ⟨u, huL, hτu⟩ := even_pow8_mem τ ht (sq_pow8 hτ)
  rw [Ne, eq_one_iff_tf] at h1 h1'
  have hc' : ∀ i, tf σ (tf τ i) = tf τ (tf σ i) := by
    intro i; rw [← tf_mul, ← tf_mul, hc]
  rw [apply_eq_iff_tf, apply_eq_iff_tf]
  simp only [hσt, hτu] at h1 h1' hc' ⊢
  exact L16_D2 t htL u huL h1 h1' hc' (e5 p)

theorem D3 : ∀ σ : Perm S5, sign σ = 1 → σ * σ = 1 → σ ≠ 1 → ∃ p : S5, σ p = p := by
  intro σ hs hσ _
  obtain ⟨t, ht, hσt⟩ := even_pow8_mem σ hs (sq_pow8 hσ)
  obtain ⟨i, hi⟩ := L16_fix t ht
  exact ⟨e5.symm i, by rw [apply_eq_iff_tf, Equiv.apply_symm_apply, hσt, hi]⟩

theorem D4 : ∀ σ : Perm S5, sign σ = 1 → σ * σ = 1 → σ ≠ 1 →
    ∀ p q : S5, σ p = p → σ q = q → p = q := by
  intro σ hs hσ h1 p q hp hq
  obtain ⟨t, ht, hσt⟩ := even_pow8_mem σ hs (sq_pow8 hσ)
  rw [Ne, eq_one_iff_tf] at h1
  rw [apply_eq_iff_tf] at hp hq
  simp only [hσt] at h1 hp hq
  exact e5.injective (L16_D4 t ht h1 _ _ hp hq)

@[expose] def a6 : P8 := swap 3 4 * swap 5 7
@[expose] def b6 : P8 := swap 3 5 * swap 4 7
@[expose] def a7 : P8 := swap 3 4 * swap 5 6
@[expose] def b7 : P8 := swap 3 5 * swap 4 6

private def ext8 (t : Fin 5 → Fin 5) (x : Fin 8) : Fin 8 :=
  if h : 3 ≤ x.val then (e5.symm (t (e5 ⟨x, h⟩))).1 else x

private theorem ofSubtype_eq_of_tab (σ : Perm S5) (t : Fin 5 → Fin 5) (hσ : ∀ i, tf σ i = t i)
    (g : P8) (hg : ∀ x, ext8 t x = g x) : ofSubtype σ = g := by
  ext1 x
  rw [← hg x, ext8]
  split_ifs with h
  · rw [Perm.ofSubtype_apply_of_mem σ (p := fun x : Fin 8 => 3 ≤ x.val) h, ← hσ, tf,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · rw [Perm.ofSubtype_apply_of_not_mem σ (p := fun x : Fin 8 => 3 ≤ x.val) h]

set_option maxRecDepth 100000 in
private theorem L16_D6 : ∀ t ∈ L16, t (e5 ⟨6, by decide⟩) = e5 ⟨6, by decide⟩ →
    (∀ x, ext8 t x = (1 : P8) x) ∨ (∀ x, ext8 t x = a6 x) ∨ (∀ x, ext8 t x = b6 x) ∨
      (∀ x, ext8 t x = (a6 * b6) x) := by
  intro t ht
  obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
private theorem L16_D7 : ∀ t ∈ L16, t (e5 ⟨7, by decide⟩) = e5 ⟨7, by decide⟩ →
    (∀ x, ext8 t x = (1 : P8) x) ∨ (∀ x, ext8 t x = a7 x) ∨ (∀ x, ext8 t x = b7 x) ∨
      (∀ x, ext8 t x = (a7 * b7) x) := by
  intro t ht
  obtain ⟨k, rfl⟩ := List.mem_iff_get.1 ht
  revert k
  decide +kernel

theorem D6 : ∀ σ : Perm S5, sign σ = 1 → σ * σ = 1 → σ ⟨6, by decide⟩ = ⟨6, by decide⟩ →
    ofSubtype σ = 1 ∨ ofSubtype σ = a6 ∨ ofSubtype σ = b6 ∨ ofSubtype σ = a6 * b6 := by
  intro σ hs hσ h6
  obtain ⟨t, ht, hσt⟩ := even_pow8_mem σ hs (sq_pow8 hσ)
  rw [apply_eq_iff_tf, hσt] at h6
  rcases L16_D6 t ht h6 with h | h | h | h
  · exact Or.inl (ofSubtype_eq_of_tab σ t hσt _ h)
  · exact Or.inr (Or.inl (ofSubtype_eq_of_tab σ t hσt _ h))
  · exact Or.inr (Or.inr (Or.inl (ofSubtype_eq_of_tab σ t hσt _ h)))
  · exact Or.inr (Or.inr (Or.inr (ofSubtype_eq_of_tab σ t hσt _ h)))

theorem D7 : ∀ σ : Perm S5, sign σ = 1 → σ * σ = 1 → σ ⟨7, by decide⟩ = ⟨7, by decide⟩ →
    ofSubtype σ = 1 ∨ ofSubtype σ = a7 ∨ ofSubtype σ = b7 ∨ ofSubtype σ = a7 * b7 := by
  intro σ hs hσ h7
  obtain ⟨t, ht, hσt⟩ := even_pow8_mem σ hs (sq_pow8 hσ)
  rw [apply_eq_iff_tf, hσt] at h7
  rcases L16_D7 t ht h7 with h | h | h | h
  · exact Or.inl (ofSubtype_eq_of_tab σ t hσt _ h)
  · exact Or.inr (Or.inl (ofSubtype_eq_of_tab σ t hσt _ h))
  · exact Or.inr (Or.inr (Or.inl (ofSubtype_eq_of_tab σ t hσt _ h)))
  · exact Or.inr (Or.inr (Or.inr (ofSubtype_eq_of_tab σ t hσt _ h)))

theorem lift_surj (g : P8) (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) :
    ∃ σ : Perm S5, ofSubtype σ = g := by
  have fix : ∀ y : Fin 8, y.val < 3 → g y = y := by
    intro y hy
    rcases (show y = 0 ∨ y = 1 ∨ y = 2 by omega) with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  have hp : ∀ x : Fin 8, 3 ≤ (g x).val ↔ 3 ≤ x.val := by
    intro x
    constructor
    · intro hgx
      by_contra hx
      have hx' : x.val < 3 := by omega
      have := fix x hx'
      rw [this] at hgx
      omega
    · intro hx
      by_contra hgx
      have hgx' : (g x).val < 3 := by omega
      have h1' : g (g x) = g x := fix _ hgx'
      have h2' : g x = x := g.injective h1'
      rw [h2'] at hgx'
      omega
  refine ⟨g.subtypePerm (fun x => hp x), ?_⟩
  refine Perm.ofSubtype_subtypePerm _ (fun x hx => ?_)
  by_contra h
  exact hx (fix x (by omega))

theorem ofS_inj : Function.Injective (ofSubtype : Perm S5 → P8) :=
  Equiv.Perm.ofSubtype_injective

theorem sq_of_pgroup (Q : Subgroup P8) (hA : Q ≤ A8s) (hP : IsPGroup 2 Q)
    (hfix : ∀ g ∈ Q, g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2) : ∀ g ∈ Q, g * g = 1 := by
  intro g hg
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hk' : g ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨σ, rfl⟩ := lift_surj g (hfix g hg).1 (hfix g hg).2.1 (hfix g hg).2.2
  have hσ : σ ^ (2 ^ k) = 1 := by
    apply ofS_inj
    rw [map_pow, hk', map_one]
  have hsign : sign σ = 1 := by
    have := mem_alternatingGroup.mp (hA hg)
    rwa [sign_ofSubtype] at this
  have hd : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hσ
  have hcard : Fintype.card (Perm S5) = 120 := by rw [Fintype.card_perm]; rfl
  have hd2 : orderOf σ ∣ 120 := hcard ▸ orderOf_dvd_card
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have hj3 : j ≤ 3 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    rw [← hjeq] at h16
    have := dvd_trans h16 hd2
    norm_num at this
  have h8 : orderOf σ ∣ 8 := by
    rw [hjeq]
    exact (pow_dvd_pow 2 hj3)
  have hσ8 : σ ^ 8 = 1 := orderOf_dvd_iff_pow_eq_one.1 h8
  have hσσ' : σ * σ = 1 := D1 σ hsign hσ8
  rw [← map_mul, hσσ', map_one]

theorem comm_of_sq (Q : Subgroup P8) (hsq : ∀ g ∈ Q, g * g = 1) :
    ∀ g ∈ Q, ∀ h ∈ Q, g * h = h * g := by
  intro g hg h hh
  have h1 := hsq (g * h) (mul_mem hg hh)
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hsq g hg)
  have hh' : h⁻¹ = h := inv_eq_of_mul_eq_one_right (hsq h hh)
  calc g * h = (g * h)⁻¹ := eq_inv_of_mul_eq_one_left h1
    _ = h * g := by rw [mul_inv_rev, hg', hh']

theorem a6_mem7 : a6 ∈ v4 3 4 5 7 := Subgroup.subset_closure (by simp [a6])
theorem b6_mem7 : b6 ∈ v4 3 4 5 7 := Subgroup.subset_closure (by simp [b6])
theorem a7_mem6 : a7 ∈ v4 3 4 5 6 := Subgroup.subset_closure (by simp [a7])
theorem b7_mem6 : b7 ∈ v4 3 4 5 6 := Subgroup.subset_closure (by simp [b7])

theorem pair_gen6 (Q : Subgroup P8) (x y : P8) (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
    (hx3 : x = a6 ∨ x = b6 ∨ x = a6 * b6) (hy3 : y = a6 ∨ y = b6 ∨ y = a6 * b6) :
    a6 ∈ Q ∧ b6 ∈ Q := by
  rcases hx3 with rfl | rfl | rfl <;> rcases hy3 with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact ⟨hx, hy⟩
  · refine ⟨hx, ?_⟩
    have e : b6 = a6 * (a6 * b6) := by decide
    rw [e]; exact mul_mem hx hy
  · exact ⟨hy, hx⟩
  · exact absurd rfl hxy
  · refine ⟨?_, hx⟩
    have e : a6 = b6 * (a6 * b6) := by decide
    rw [e]; exact mul_mem hx hy
  · refine ⟨hy, ?_⟩
    have e : b6 = (a6 * b6) * a6 := by decide
    rw [e]; exact mul_mem hx hy
  · refine ⟨?_, hy⟩
    have e : a6 = (a6 * b6) * b6 := by decide
    rw [e]; exact mul_mem hx hy
  · exact absurd rfl hxy

theorem pair_gen7 (Q : Subgroup P8) (x y : P8) (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
    (hx3 : x = a7 ∨ x = b7 ∨ x = a7 * b7) (hy3 : y = a7 ∨ y = b7 ∨ y = a7 * b7) :
    a7 ∈ Q ∧ b7 ∈ Q := by
  rcases hx3 with rfl | rfl | rfl <;> rcases hy3 with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact ⟨hx, hy⟩
  · refine ⟨hx, ?_⟩
    have e : b7 = a7 * (a7 * b7) := by decide
    rw [e]; exact mul_mem hx hy
  · exact ⟨hy, hx⟩
  · exact absurd rfl hxy
  · refine ⟨?_, hx⟩
    have e : a7 = b7 * (a7 * b7) := by decide
    rw [e]; exact mul_mem hx hy
  · refine ⟨hy, ?_⟩
    have e : b7 = (a7 * b7) * a7 := by decide
    rw [e]; exact mul_mem hx hy
  · refine ⟨?_, hy⟩
    have e : a7 = (a7 * b7) * b7 := by decide
    rw [e]; exact mul_mem hx hy
  · exact absurd rfl hxy

theorem dd_inv_stab : ∀ y : Fin 8, 3 ≤ y.val → 3 ≤ (dd⁻¹ y).val := by decide
theorem dd_inv_fix : ∀ y : Fin 8, 3 ≤ y.val → dd⁻¹ y = y → 6 ≤ y.val := by decide

theorem dd_conj_a6 : dd * a6 * dd⁻¹ ≠ a6 := by decide
theorem dd_conj_b6 : dd * b6 * dd⁻¹ ≠ b6 := by decide
theorem dd_conj_ab6 : dd * (a6 * b6) * dd⁻¹ ≠ a6 * b6 := by decide
theorem dd_conj_a7 : dd * a7 * dd⁻¹ ≠ a7 := by decide
theorem dd_conj_b7 : dd * b7 * dd⁻¹ ≠ b7 := by decide
theorem dd_conj_ab7 : dd * (a7 * b7) * dd⁻¹ ≠ a7 * b7 := by decide

theorem T1 (Q : Subgroup P8) (hA : Q ≤ A8s) (hP : IsPGroup 2 Q)
    (hfix : ∀ g ∈ Q, g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2) (hdd : ∀ g ∈ Q, dd * g * dd⁻¹ ∈ Q) :
    Q = ⊥ ∨ Q = v4 3 4 5 6 ∨ Q = v4 3 4 5 7 := by
  by_cases hQ : Q = ⊥
  · exact Or.inl hQ
  right
  have hsq := sq_of_pgroup Q hA hP hfix
  have hcomm := comm_of_sq Q hsq
  obtain ⟨g0, hg0Q, hg0⟩ : ∃ g0 ∈ Q, g0 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hQ (eq_bot_iff.2 fun g hg => (Subgroup.mem_bot).2 (hcon g hg))
  obtain ⟨σ0, hσ0⟩ := lift_surj g0 (hfix g0 hg0Q).1 (hfix g0 hg0Q).2.1 (hfix g0 hg0Q).2.2
  have hσ0ne : σ0 ≠ 1 := by
    rintro rfl
    exact hg0 (by rw [← hσ0, map_one])
  have hσ0sq : σ0 * σ0 = 1 := by
    apply ofS_inj
    rw [map_mul, hσ0, map_one]
    exact hsq g0 hg0Q
  have hσ0sign : sign σ0 = 1 := by
    have := mem_alternatingGroup.mp (hA hg0Q)
    rwa [← hσ0, sign_ofSubtype] at this
  obtain ⟨p0, hp0⟩ := D3 σ0 hσ0sign hσ0sq hσ0ne
  have hfixp0 : ∀ g ∈ Q, g ≠ 1 → ∀ σ : Perm S5, ofSubtype σ = g → σ p0 = p0 := by
    intro g hg hg1 σ hσ
    have hσσ : σ * σ = 1 := by
      apply ofS_inj
      rw [map_mul, hσ, map_one]
      exact hsq g hg
    have hsign : sign σ = 1 := by
      have := mem_alternatingGroup.mp (hA hg)
      rwa [← hσ, sign_ofSubtype] at this
    have hne : σ ≠ 1 := by
      rintro rfl
      exact hg1 (by rw [← hσ, map_one])
    have hcomm' : σ0 * σ = σ * σ0 := by
      apply ofS_inj
      rw [map_mul, map_mul, hσ0, hσ]
      exact hcomm g0 hg0Q g hg
    exact D2 σ0 σ hσ0sign hsign hσ0sq hσσ hσ0ne hne hcomm' p0 hp0
  have hc1 : dd * g0 * dd⁻¹ ∈ Q := hdd g0 hg0Q
  have hc1ne : dd * g0 * dd⁻¹ ≠ 1 := by
    intro h
    apply hg0
    calc g0 = dd⁻¹ * (dd * g0 * dd⁻¹) * dd := by group
      _ = 1 := by rw [h]; group
  have hp0_dd : (p0 : Fin 8).val = 6 ∨ (p0 : Fin 8).val = 7 := by
    obtain ⟨σ1, hσ1⟩ := lift_surj _ (hfix _ hc1).1 (hfix _ hc1).2.1 (hfix _ hc1).2.2
    have hσ1p := hfixp0 _ hc1 hc1ne σ1 hσ1
    have hA1 : (dd * g0 * dd⁻¹) (p0 : Fin 8) = (p0 : Fin 8) := by
      have h := ofSubtype_apply_of_mem σ1 p0.2
      rw [hσ1p] at h
      rw [← hσ1, h]
    have h1 : dd (g0 (dd⁻¹ (p0 : Fin 8))) = (p0 : Fin 8) := by
      simpa [Perm.mul_apply] using hA1
    have hx : g0 (dd⁻¹ (p0 : Fin 8)) = dd⁻¹ (p0 : Fin 8) := by
      have h2 := congrArg (fun y => dd⁻¹ y) h1
      simpa using h2
    have hxS : 3 ≤ (dd⁻¹ (p0 : Fin 8)).val := dd_inv_stab _ p0.2
    have hσ0x : σ0 ⟨dd⁻¹ (p0 : Fin 8), hxS⟩ = ⟨dd⁻¹ (p0 : Fin 8), hxS⟩ := by
      apply Subtype.ext
      have h := ofSubtype_apply_of_mem σ0 hxS
      rw [hσ0, hx] at h
      exact h.symm
    have heq := D4 σ0 hσ0sign hσ0sq hσ0ne _ p0 hσ0x hp0
    have hval := congrArg (fun z : S5 => (z : Fin 8)) heq
    have hfix6 := dd_inv_fix _ p0.2 hval
    have := (p0 : Fin 8).isLt
    omega
  have hg1L' : dd * g0 * dd⁻¹ ∈ Q := hc1
  rcases hp0_dd with h6 | h7
  ·
    have hL : ∀ g ∈ Q, g ≠ 1 → g = a6 ∨ g = b6 ∨ g = a6 * b6 := by
      intro g hg hg1
      obtain ⟨σ, hσ⟩ := lift_surj g (hfix g hg).1 (hfix g hg).2.1 (hfix g hg).2.2
      have hp6 : p0 = ⟨6, by decide⟩ := Subtype.ext (Fin.ext h6)
      have hfix6 : σ ⟨6, by decide⟩ = ⟨6, by decide⟩ := by
        rw [← hp6]
        exact hfixp0 g hg hg1 σ hσ
      have hsign : sign σ = 1 := by
        have := mem_alternatingGroup.mp (hA hg)
        rwa [← hσ, sign_ofSubtype] at this
      have hσσ : σ * σ = 1 := by
        apply ofS_inj
        rw [map_mul, hσ, map_one]
        exact hsq g hg
      rcases D6 σ hsign hσσ hfix6 with h | h | h | h
      · exact absurd (hσ.symm.trans h) hg1
      · exact Or.inl (hσ.symm.trans h)
      · exact Or.inr (Or.inl (hσ.symm.trans h))
      · exact Or.inr (Or.inr (hσ.symm.trans h))
    have hQle : Q ≤ v4 3 4 5 7 := by
      intro g hg
      by_cases hg1 : g = 1
      · rw [hg1]
        exact one_mem _
      · rcases hL g hg hg1 with rfl | rfl | rfl
        · exact a6_mem7
        · exact b6_mem7
        · exact mul_mem a6_mem7 b6_mem7
    have hg0L := hL g0 hg0Q hg0
    have hg1L := hL _ hc1 hc1ne
    have hne : g0 ≠ dd * g0 * dd⁻¹ := by
      intro e
      rcases hg0L with h | h | h <;> rw [h] at e
      · exact dd_conj_a6 e.symm
      · exact dd_conj_b6 e.symm
      · exact dd_conj_ab6 e.symm
    have hpair := pair_gen6 Q g0 (dd * g0 * dd⁻¹) hg0Q hc1 hne hg0L hg1L
    have hvQ : v4 3 4 5 7 ≤ Q := by
      show Subgroup.closure ({a6, b6} : Set P8) ≤ Q
      exact (Subgroup.closure_le Q).2 (Set.insert_subset_iff.2 ⟨hpair.1, Set.singleton_subset_iff.2 hpair.2⟩)
    exact Or.inr (le_antisymm hQle hvQ)
  ·
    have hL : ∀ g ∈ Q, g ≠ 1 → g = a7 ∨ g = b7 ∨ g = a7 * b7 := by
      intro g hg hg1
      obtain ⟨σ, hσ⟩ := lift_surj g (hfix g hg).1 (hfix g hg).2.1 (hfix g hg).2.2
      have hp7 : p0 = ⟨7, by decide⟩ := Subtype.ext (Fin.ext h7)
      have hfix7 : σ ⟨7, by decide⟩ = ⟨7, by decide⟩ := by
        rw [← hp7]
        exact hfixp0 g hg hg1 σ hσ
      have hsign : sign σ = 1 := by
        have := mem_alternatingGroup.mp (hA hg)
        rwa [← hσ, sign_ofSubtype] at this
      have hσσ : σ * σ = 1 := by
        apply ofS_inj
        rw [map_mul, hσ, map_one]
        exact hsq g hg
      rcases D7 σ hsign hσσ hfix7 with h | h | h | h
      · exact absurd (hσ.symm.trans h) hg1
      · exact Or.inl (hσ.symm.trans h)
      · exact Or.inr (Or.inl (hσ.symm.trans h))
      · exact Or.inr (Or.inr (hσ.symm.trans h))
    have hQle : Q ≤ v4 3 4 5 6 := by
      intro g hg
      by_cases hg1 : g = 1
      · rw [hg1]
        exact one_mem _
      · rcases hL g hg hg1 with rfl | rfl | rfl
        · exact a7_mem6
        · exact b7_mem6
        · exact mul_mem a7_mem6 b7_mem6
    have hg0L := hL g0 hg0Q hg0
    have hg1L := hL _ hc1 hc1ne
    have hne : g0 ≠ dd * g0 * dd⁻¹ := by
      intro e
      rcases hg0L with h | h | h <;> rw [h] at e
      · exact dd_conj_a7 e.symm
      · exact dd_conj_b7 e.symm
      · exact dd_conj_ab7 e.symm
    have hpair := pair_gen7 Q g0 (dd * g0 * dd⁻¹) hg0Q hc1 hne hg0L hg1L
    have hvQ : v4 3 4 5 6 ≤ Q := by
      show Subgroup.closure ({a7, b7} : Set P8) ≤ Q
      exact (Subgroup.closure_le Q).2 (Set.insert_subset_iff.2 ⟨hpair.1, Set.singleton_subset_iff.2 hpair.2⟩)
    exact Or.inl (le_antisymm hQle hvQ)

theorem cc_0 : cc 0 = 1 := by decide
theorem cc_1 : cc 1 = 2 := by decide
theorem cc_2 : cc 2 = 0 := by decide
theorem no_pow2_of_three_orbit (g : P8) (x : Fin 8) (hk : ∃ k, g ^ (2 ^ k) = 1)
    (h3 : (g ^ 3) x = x) (h1 : g x ≠ x) (h2 : g (g x) ≠ x) : False := by
  have hm : ∀ m : ℕ, (g ^ (3 * m)) x = x := fun m => by
    rw [pow_mul]; exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h3 m
  have key2 : ∀ n : ℕ, (g ^ n) x = (g ^ (n % 3)) x := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n 3]
    rw [pow_add, Perm.mul_apply, hm]
  obtain ⟨k, hk⟩ := hk
  have hmod : 2 ^ k % 3 ≠ 0 := by
    intro h
    have h3' : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3'
    norm_num at this
  have hz : (g ^ (2 ^ k % 3)) x = x := by
    rw [← key2, hk, Equiv.Perm.one_apply]
  rcases (show 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 by omega) with hr | hr
  · rw [hr, pow_one] at hz; exact h1 hz
  · rw [hr, pow_two, Perm.mul_apply] at hz; exact h2 hz

theorem fix_of_cent_three (c g : P8) (p q r : Fin 8) (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hcpq : c p = q) (hcqr : c q = r) (hcrp : c r = p)
    (hout : ∀ a, a ≠ p → a ≠ q → a ≠ r → c a = a) (hgc : g * c = c * g)
    (hpow : ∃ k, g ^ (2 ^ k) = 1) : g p = p ∧ g q = q ∧ g r = r := by
  have hgc' : ∀ x, g (c x) = c (g x) := fun x => by
    have := congrArg (fun h : P8 => h x) hgc
    simpa [Perm.mul_apply] using this
  have h1 : g q = c (g p) := by have := hgc' p; rwa [hcpq] at this
  have h2 : g r = c (g q) := by have := hgc' q; rwa [hcqr] at this
  have hin : g p = p ∨ g p = q ∨ g p = r := by
    by_contra hc
    push Not at hc
    have hcg : c (g p) = g p := hout _ hc.1 hc.2.1 hc.2.2
    exact hpq (g.injective (h1.trans hcg)).symm
  rcases hin with hp | hp | hp
  · have hq : g q = q := by rw [h1, hp, hcpq]
    have hr : g r = r := by rw [h2, hq, hcqr]
    exact ⟨hp, hq, hr⟩
  · exfalso
    have hgq : g q = r := by rw [h1, hp, hcqr]
    have hgr : g r = p := by rw [h2, hgq, hcrp]
    exact no_pow2_of_three_orbit g p hpow
      (by simp only [pow_three, Perm.mul_apply]; rw [hp, hgq, hgr])
      (by rw [hp]; exact fun h => hpq h.symm)
      (by rw [hp, hgq]; exact hrp)
  · exfalso
    have hgq : g q = p := by rw [h1, hp, hcrp]
    have hgr : g r = q := by rw [h2, hgq, hcpq]
    exact no_pow2_of_three_orbit g p hpow
      (by simp only [pow_three, Perm.mul_apply]; rw [hp, hgr, hgq])
      (by rw [hp]; exact hrp)
      (by rw [hp, hgr]; exact fun h => hpq h.symm)

theorem hout_cc : ∀ a : Fin 8, a ≠ 0 → a ≠ 1 → a ≠ 2 → cc a = a := by decide
theorem hout_dd : ∀ a : Fin 8, a ≠ 3 → a ≠ 4 → a ≠ 5 → dd a = a := by decide
theorem dd_3 : dd 3 = 4 := by decide
theorem dd_4 : dd 4 = 5 := by decide
theorem dd_5 : dd 5 = 3 := by decide

theorem fix012_of_cent_cc (g : P8) (hg : g * cc = cc * g) (hpow : ∃ k, g ^ (2 ^ k) = 1) :
    g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2 :=
  fix_of_cent_three cc g 0 1 2 (by decide) (by decide) (by decide) cc_0 cc_1 cc_2 hout_cc hg hpow

theorem fix345_of_cent_dd (g : P8) (hg : g * dd = dd * g) (hpow : ∃ k, g ^ (2 ^ k) = 1) :
    g 3 = 3 ∧ g 4 = 4 ∧ g 5 = 5 :=
  fix_of_cent_three dd g 3 4 5 (by decide) (by decide) (by decide) dd_3 dd_4 dd_5 hout_dd hg hpow

theorem v4_gen1 (a b c d : Fin 8) : swap a b * swap c d ∈ v4 a b c d :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem v4_gen2 (a b c d : Fin 8) : swap a c * swap b d ∈ v4 a b c d :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem v4_closure_le (a b c d : Fin 8) (K : Subgroup P8) (h1 : swap a b * swap c d ∈ K)
    (h2 : swap a c * swap b d ∈ K) : v4 a b c d ≤ K := by
  unfold v4
  exact (Subgroup.closure_le K).2 (Set.insert_subset_iff.2 ⟨h1, Set.singleton_subset_iff.2 h2⟩)

@[expose] def nn : P8 := swap 0 3 * swap 1 4 * swap 2 5 * swap 6 7

@[expose] def phi : P8 →* P8 := (MulAut.conj nn).toMonoidHom

theorem nn_sq : nn * nn = 1 := by decide
theorem dd_eq_conj : dd = nn * cc * nn⁻¹ := by decide

theorem phi_apply (x : P8) : phi x = nn * x * nn⁻¹ := rfl

theorem phi_phi (x : P8) : phi (phi x) = x := by
  rw [phi_apply, phi_apply]
  calc nn * (nn * x * nn⁻¹) * nn⁻¹ = (nn * nn) * x * (nn * nn)⁻¹ := by group
    _ = x := by rw [nn_sq]; simp

theorem phi_V3456 : (v4 3 4 5 6).map phi = v4 0 1 2 7 := by
  have e1 : phi (swap 3 4 * swap 5 6) = swap 0 1 * swap 2 7 := by decide
  have e2 : phi (swap 3 5 * swap 4 6) = swap 0 2 * swap 1 7 := by decide
  unfold v4
  rw [MonoidHom.map_closure, Set.image_pair, e1, e2]

theorem phi_V3457 : (v4 3 4 5 7).map phi = v4 0 1 2 6 := by
  have e1 : phi (swap 3 4 * swap 5 7) = swap 0 1 * swap 2 6 := by decide
  have e2 : phi (swap 3 5 * swap 4 7) = swap 0 2 * swap 1 6 := by decide
  unfold v4
  rw [MonoidHom.map_closure, Set.image_pair, e1, e2]

theorem T2 (Q : Subgroup P8) (hA : Q ≤ A8s) (hP : IsPGroup 2 Q)
    (hfix : ∀ g ∈ Q, g 3 = 3 ∧ g 4 = 4 ∧ g 5 = 5) (hcc : ∀ g ∈ Q, cc * g * cc⁻¹ ∈ Q) :
    Q = ⊥ ∨ Q = v4 0 1 2 6 ∨ Q = v4 0 1 2 7 := by
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Subgroup P8, Q' = Q.map phi := ⟨_, rfl⟩
  have hN : A8s.Normal := by unfold A8s; infer_instance
  have hA' : Q' ≤ A8s := by
    intro g hg
    rw [hQ'] at hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    exact Subgroup.Normal.conj_mem hN y (hA hy) nn
  have hP' : IsPGroup 2 Q' := by
    rw [hQ']
    exact hP.map phi
  have hfix' : ∀ g ∈ Q', g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2 := by
    intro g hg
    rw [hQ'] at hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨h3, h4, h5⟩ := hfix y hy
    have e0 : nn⁻¹ 0 = 3 := by decide
    have e1 : nn⁻¹ 1 = 4 := by decide
    have e2 : nn⁻¹ 2 = 5 := by decide
    have f0 : nn 3 = 0 := by decide
    have f1 : nn 4 = 1 := by decide
    have f2 : nn 5 = 2 := by decide
    refine ⟨?_, ?_, ?_⟩
    · show nn (y (nn⁻¹ 0)) = 0
      rw [e0, h3, f0]
    · show nn (y (nn⁻¹ 1)) = 1
      rw [e1, h4, f1]
    · show nn (y (nn⁻¹ 2)) = 2
      rw [e2, h5, f2]
  have hdd' : ∀ g ∈ Q', dd * g * dd⁻¹ ∈ Q' := by
    intro g hg
    rw [hQ'] at hg ⊢
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    refine Subgroup.mem_map.2 ⟨cc * y * cc⁻¹, hcc y hy, ?_⟩
    rw [phi_apply, phi_apply, dd_eq_conj]
    group
  have hinj : Function.Injective phi := (MulAut.conj nn).injective
  have hQmem : ∀ x, phi x ∈ Q' → x ∈ Q := by
    intro x hx
    rw [hQ'] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have : y = x := hinj hyx
    exact this ▸ hy
  rcases T1 Q' hA' hP' hfix' hdd' with h | h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : phi x ∈ Q' := by rw [hQ']; exact Subgroup.mem_map_of_mem phi hx
    rw [h, Subgroup.mem_bot] at hx'
    calc x = phi (phi x) := (phi_phi x).symm
      _ = 1 := by rw [hx', map_one]
  · right; right
    refine le_antisymm (fun x hx => ?_) (v4_closure_le 0 1 2 7 Q ?_ ?_)
    · have h1 : phi x ∈ Q' := by rw [hQ']; exact Subgroup.mem_map_of_mem phi hx
      rw [h] at h1
      have h2 := Subgroup.mem_map_of_mem phi h1
      rw [phi_V3456, phi_phi] at h2
      exact h2
    · apply hQmem
      rw [h, show phi (swap 0 1 * swap 2 7) = swap 3 4 * swap 5 6 by decide]
      exact v4_gen1 _ _ _ _
    · apply hQmem
      rw [h, show phi (swap 0 2 * swap 1 7) = swap 3 5 * swap 4 6 by decide]
      exact v4_gen2 _ _ _ _
  · right; left
    refine le_antisymm (fun x hx => ?_) (v4_closure_le 0 1 2 6 Q ?_ ?_)
    · have h1 : phi x ∈ Q' := by rw [hQ']; exact Subgroup.mem_map_of_mem phi hx
      rw [h] at h1
      have h2 := Subgroup.mem_map_of_mem phi h1
      rw [phi_V3457, phi_phi] at h2
      exact h2
    · apply hQmem
      rw [h, show phi (swap 0 1 * swap 2 6) = swap 3 4 * swap 5 7 by decide]
      exact v4_gen1 _ _ _ _
    · apply hQmem
      rw [h, show phi (swap 0 2 * swap 1 6) = swap 3 5 * swap 4 7 by decide]
      exact v4_gen2 _ _ _ _

theorem ct_cc : cc.cycleType = {3} := by
  rw [show cc = swap 1 0 * swap 1 2 by decide]
  exact (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType

theorem ct_dd : dd.cycleType = {3} := by
  rw [show dd = swap 4 3 * swap 4 5 by decide]
  exact (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType

theorem disj_cc_dd : Equiv.Perm.Disjoint cc dd := by
  intro x
  fin_cases x <;> decide

theorem ct_m1 : (cc * dd).cycleType = {3, 3} := by
  rw [disj_cc_dd.cycleType_mul, ct_cc, ct_dd]
  rfl

theorem card_cent_m1 : Nat.card (Subgroup.centralizer ({cc * dd} : Set P8)) = 36 := by
  rw [Equiv.Perm.nat_card_centralizer, ct_m1]
  decide

theorem m1_eq : m₁ = cc * dd := by decide
theorem m2_eq : m₂ = cc * (dd * dd) := by decide

open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb Nor conjBy CenS)

theorem comm_of_conj {e t : P8} (h : e * t * e⁻¹ = t) : t * e = e * t := by
  calc t * e = (e * t * e⁻¹) * e := by rw [h]
    _ = e * t := by group

theorem dd_sq_cycle : (dd * dd).cycleType = {3} := by
  rw [show dd * dd = swap 3 4 * swap 3 5 by decide]
  exact (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType

theorem disj_cc_dd2 : Equiv.Perm.Disjoint cc (dd * dd) := by
  intro x
  fin_cases x <;> decide

theorem ct_m2 : (cc * (dd * dd)).cycleType = {3, 3} := by
  rw [disj_cc_dd2.cycleType_mul, ct_cc, dd_sq_cycle]
  rfl

theorem card_cent_m2 : Nat.card (Subgroup.centralizer ({cc * (dd * dd)} : Set P8)) = 36 := by
  rw [Equiv.Perm.nat_card_centralizer, ct_m2]
  decide

theorem card_cent_A8 (m : P8) (hC : Nat.card (Subgroup.centralizer ({m} : Set P8)) = 36)
    (hτ : swap 6 7 ∈ Subgroup.centralizer ({m} : Set P8)) :
    Nat.card ↥(Subgroup.centralizer ({m} : Set P8) ⊓ A8s) = 18 := by
  set C := Subgroup.centralizer ({m} : Set P8) with hCdef
  let g : C →* ℤˣ := (Equiv.Perm.sign : P8 →* ℤˣ).comp C.subtype
  have hmap : g.ker.map C.subtype = C ⊓ A8s := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, mem_alternatingGroup.2 (by simpa [g] using hy)⟩
    · rintro ⟨hxC, hxA⟩
      exact ⟨⟨x, hxC⟩, by simpa [g] using mem_alternatingGroup.1 hxA, rfl⟩
  have hsurj : Function.Surjective g := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one g⟩
    · exact ⟨⟨swap 6 7, hτ⟩, by simp [g, sign_swap (show (6 : Fin 8) ≠ 7 by decide)]⟩
  have hunits : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, -1, by decide, Set.eq_univ_of_forall fun u => ?_⟩
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  have hidx : g.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, hunits]
  have hkc : Nat.card g.ker = 18 := by
    have h1 := Subgroup.card_mul_index g.ker
    rw [hidx, hC] at h1
    omega
  have hmap_card : Nat.card ↥(C ⊓ A8s) = Nat.card g.ker := by
    rw [← hmap]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective g.ker C.subtype Subtype.val_injective).toEquiv).symm
  rw [hmap_card, hkc]

theorem dvd_two_of_dvd_18 (R : Subgroup P8) (hR : IsPGroup 2 R) (hd : Nat.card R ∣ 18) :
    Nat.card R ∣ 2 := by
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  rw [hk] at hd ⊢
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have := pow_dvd_pow 2 (show k ≤ 1 by omega)
    simpa using this
  · exfalso
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
    have := dvd_trans h4 hd
    norm_num at this

theorem card_dvd_two (Y : Subgroup P8) (hYA : Y ≤ A8s) (hY2 : IsPGroup 2 Y) (m : P8)
    (hC : Nat.card (Subgroup.centralizer ({m} : Set P8)) = 36)
    (hτ : swap 6 7 ∈ Subgroup.centralizer ({m} : Set P8)) :
    Nat.card ↥(Y ⊓ Subgroup.centralizer ({m} : Set P8)) ∣ 2 := by
  apply dvd_two_of_dvd_18 _ hY2.to_inf_left
  rw [← card_cent_A8 m hC hτ]
  exact Subgroup.card_dvd_of_le (le_inf inf_le_right (inf_le_left.trans hYA))

theorem eq_of_card_two (R : Subgroup P8) (h : Nat.card R = 2) {t s : P8} (ht : t ∈ R)
    (hs : s ∈ R) (ht1 : t ≠ 1) (hs1 : s ≠ 1) : s = t := by
  obtain ⟨x, y, hxy, hU⟩ := Nat.card_eq_two_iff.1 h
  have hmem : ∀ z : R, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set R) := by rw [hU]; exact Set.mem_univ z
    simpa using this
  have h1 := hmem ⟨1, R.one_mem⟩
  have h2 := hmem ⟨t, ht⟩
  have h3 := hmem ⟨s, hs⟩
  have ht' : (⟨t, ht⟩ : R) ≠ ⟨1, R.one_mem⟩ := fun h => ht1 (congrArg Subtype.val h)
  have hs' : (⟨s, hs⟩ : R) ≠ ⟨1, R.one_mem⟩ := fun h => hs1 (congrArg Subtype.val h)
  have key : (⟨s, hs⟩ : R) = ⟨t, ht⟩ := by
    rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;> rcases h3 with e3 | e3 <;>
      first
      | exact absurd (e2.trans e1.symm) ht'
      | exact absurd (e3.trans e1.symm) hs'
      | exact e3.trans e2.symm
  exact congrArg Subtype.val key

theorem R_bot {Y : Subgroup P8} {m : P8} (hYA : Y ≤ A8s) (hY2 : IsPGroup 2 Y)
    (hcc : cc ∈ Subgroup.normalizer (Y : Set P8)) (hdd : dd ∈ Subgroup.normalizer (Y : Set P8))
    (hmcc : cc * m = m * cc) (hmdd : dd * m = m * dd)
    (hcard : Nat.card ↥(Y ⊓ Subgroup.centralizer ({m} : Set P8)) ∣ 2) :
    Y ⊓ Subgroup.centralizer ({m} : Set P8) = ⊥ := by
  by_contra hne
  have hcard1 : Nat.card ↥(Y ⊓ Subgroup.centralizer ({m} : Set P8)) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hcard with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hne
    · exact h
  obtain ⟨t, htR, ht1⟩ : ∃ t ∈ Y ⊓ Subgroup.centralizer ({m} : Set P8), t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_bot_iff.2 fun g hg => (Subgroup.mem_bot).2 (hcon g hg))
  have hconj : ∀ e : P8, e ∈ Subgroup.normalizer (Y : Set P8) → e * m = m * e →
      e * t * e⁻¹ = t := by
    intro e he hem
    obtain ⟨htY, htC⟩ := Subgroup.mem_inf.1 htR
    have hsY : e * t * e⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 he t).1 htY
    have htm : Commute t m := Subgroup.mem_centralizer_singleton_iff.1 htC
    have hc : Commute (e * t * e⁻¹) m :=
      ((show Commute e m from hem).mul_left htm).mul_left (show Commute e m from hem).inv_left
    have hsC : e * t * e⁻¹ ∈ Subgroup.centralizer ({m} : Set P8) :=
      Subgroup.mem_centralizer_singleton_iff.2 hc
    have hs1 : e * t * e⁻¹ ≠ 1 := fun h => ht1 (by
      calc t = e⁻¹ * (e * t * e⁻¹) * e⁻¹⁻¹ := by group
        _ = 1 := by rw [h]; group)
    exact eq_of_card_two _ hcard1 htR (Subgroup.mem_inf.2 ⟨hsY, hsC⟩) ht1 hs1
  have hcc_t : cc * t * cc⁻¹ = t := hconj cc hcc hmcc
  have hdd_t : dd * t * dd⁻¹ = t := hconj dd hdd hmdd
  have hC : t ∈ CenS Pm :=
    (mem_CenS_Pm_iff t).2 ⟨comm_of_conj hcc_t, comm_of_conj hdd_t⟩
  have ht2 : t ^ 2 = 1 := by
    have hsq : t ^ 2 ∈ Y ⊓ Subgroup.centralizer ({m} : Set P8) := pow_mem htR 2
    by_contra hne2
    have h := eq_of_card_two _ hcard1 htR hsq ht1 hne2
    have : t * t = t * 1 := by rw [mul_one, ← pow_two]; exact h
    exact ht1 (mul_left_cancel this)
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have ht67 : t = swap 6 7 := A_cent_P_inv_involution t hC hord
  have htA : t ∈ A8s := hYA (Subgroup.mem_inf.1 htR).1
  have hsgn := mem_alternatingGroup.1 htA
  rw [ht67, sign_swap (show (6 : Fin 8) ≠ 7 by decide)] at hsgn
  exact absurd hsgn (by decide)

theorem pow2_of_mem {Y : Subgroup P8} (hY2 : IsPGroup 2 Y) {g : P8} (hg : g ∈ Y) :
    ∃ k, g ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hY2 ⟨g, hg⟩
  refine ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem no_order3 {Y : Subgroup P8} (hY2 : IsPGroup 2 Y) {g : P8} (hg : g ∈ Y)
    (h3 : g ^ 3 = 1) (hg1 : g ≠ 1) : False := by
  obtain ⟨k, hk⟩ := pow2_of_mem hY2 hg
  have hc : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by decide)
  have key : g ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨h3, hk⟩
  rw [Nat.Coprime.gcd_eq_one hc, pow_one] at key
  exact hg1 key

theorem sub_of_sq (Y : Subgroup P8) {x y : P8} (h : x = y * y) :
    Y ⊓ Subgroup.centralizer ({y} : Set P8) ≤ Y ⊓ Subgroup.centralizer ({x} : Set P8) := by
  intro g hg
  obtain ⟨hgY, hgC⟩ := Subgroup.mem_inf.1 hg
  refine Subgroup.mem_inf.2 ⟨hgY, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hgC ⊢
  rw [h]
  exact (show Commute g y from hgC).mul_right (show Commute g y from hgC)

theorem conj_cent {e c g : P8} (hec : Commute e c) (hgc : Commute g c) :
    Commute (e * g * e⁻¹) c :=
  (hec.mul_left hgc).mul_left hec.inv_left

@[expose] def Slist : List P8 :=
  [1, cc, cc * cc, dd, dd * dd, cc * dd, cc * (dd * dd), cc * cc * dd, cc * cc * (dd * dd)]

private theorem Slist_mul_chk : ∀ i j : Fin Slist.length, ∃ k : Fin Slist.length,
    ∀ x : Fin 8, (Slist.get i * Slist.get j) x = Slist.get k x := by
  decide +kernel

private theorem Slist_inv_chk : ∀ i : Fin Slist.length, ∃ k : Fin Slist.length,
    ∀ x : Fin 8, (Slist.get i)⁻¹ x = Slist.get k x := by
  decide +kernel

private theorem Slist_pow3_chk : ∀ i : Fin Slist.length, ∀ x : Fin 8, (Slist.get i ^ 3) x = x := by
  decide +kernel

private theorem Slist_comm_chk : ∀ i j : Fin Slist.length,
    ∀ x : Fin 8, (Slist.get i * Slist.get j) x = (Slist.get j * Slist.get i) x := by
  decide +kernel

theorem Slist_mul : ∀ a ∈ Slist, ∀ b ∈ Slist, a * b ∈ Slist := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ha
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hb
  obtain ⟨k, hk⟩ := Slist_mul_chk i j
  rw [Equiv.ext hk]
  exact List.get_mem _ _
theorem Slist_inv : ∀ a ∈ Slist, a⁻¹ ∈ Slist := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ha
  obtain ⟨k, hk⟩ := Slist_inv_chk i
  rw [Equiv.ext hk]
  exact List.get_mem _ _
theorem Slist_pow3 : ∀ a ∈ Slist, a ^ 3 = 1 := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ha
  exact Equiv.ext (Slist_pow3_chk i)
theorem Slist_comm : ∀ a ∈ Slist, ∀ b ∈ Slist, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ha
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hb
  exact Equiv.ext (Slist_comm_chk i j)

@[expose] def Ks : Subgroup P8 where
  carrier := {x | x ∈ Slist}
  mul_mem' := fun {a b} ha hb => Slist_mul a ha b hb
  one_mem' := by
    show (1 : P8) ∈ Slist
    exact List.mem_cons_self
  inv_mem' := fun {a} ha => Slist_inv a ha

theorem m1_mem_Eo : m₁ ∈ Eo := Subgroup.subset_closure (Set.mem_insert _ _)
theorem m2_mem_Eo : m₂ ∈ Eo := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem Eo_le_Ks : Eo ≤ Ks := by
  show Subgroup.closure ({m₁, m₂} : Set P8) ≤ Ks
  refine (Subgroup.closure_le Ks).2 ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · show m₁ ∈ Slist
    rw [m1_eq]; decide
  · show m₂ ∈ Slist
    rw [m2_eq]; decide

theorem Eo_mem {a : P8} (ha : a ∈ Eo) : a ∈ Slist := Eo_le_Ks ha

theorem cc_eq_Eo : cc = m₁ ^ 2 * m₂ ^ 2 := by rw [m1_eq, m2_eq]; decide
theorem dd_eq_Eo : dd = m₁ ^ 2 * m₂ := by rw [m1_eq, m2_eq]; decide

theorem cc_mem_Eo : cc ∈ Eo := by
  rw [cc_eq_Eo]; exact mul_mem (pow_mem m1_mem_Eo 2) (pow_mem m2_mem_Eo 2)

theorem dd_mem_Eo : dd ∈ Eo := by
  rw [dd_eq_Eo]; exact mul_mem (pow_mem m1_mem_Eo 2) m2_mem_Eo

theorem Ks_le_Eo : Ks ≤ Eo := by
  intro x hx
  have hx' : x ∈ Slist := hx
  simp only [Slist, List.mem_cons, List.mem_nil_iff, or_false] at hx'
  rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact cc_mem_Eo
  · exact mul_mem cc_mem_Eo cc_mem_Eo
  · exact dd_mem_Eo
  · exact mul_mem dd_mem_Eo dd_mem_Eo
  · exact mul_mem cc_mem_Eo dd_mem_Eo
  · exact mul_mem cc_mem_Eo (mul_mem dd_mem_Eo dd_mem_Eo)
  · exact mul_mem (mul_mem cc_mem_Eo cc_mem_Eo) dd_mem_Eo
  · exact mul_mem (mul_mem cc_mem_Eo cc_mem_Eo) (mul_mem dd_mem_Eo dd_mem_Eo)

theorem Eo_card9 : 9 ≤ Nat.card Eo := by
  have hK : Nat.card Ks = 9 := by
    have h1 : (Ks : Set P8) = ((Slist.toFinset : Finset P8) : Set P8) := by
      ext x
      simp [Ks, Slist]
    have h2 : Nat.card Ks = (Ks : Set P8).ncard := Nat.card_coe_set_eq _
    rw [h2, h1, Set.ncard_coe_finset]
    decide
  rw [← hK]
  exact Subgroup.card_le_of_le Ks_le_Eo

instance Eo_isEA : CFSG.IsElementaryAbelian 3 Eo := by
  have hH : ∀ a : Eo, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using Slist_pow3 _ (Eo_mem a.2))
  have hc : IsMulCommutative Eo :=
    ⟨⟨fun a b => Subtype.ext (Slist_comm _ (Eo_mem a.2) _ (Eo_mem b.2))⟩⟩
  exact { toIsMulCommutative := hc, exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hH }

theorem nor_of_gens {U : Subgroup P8} {g : P8} (hU : ∀ h ∈ U, g * h * g⁻¹ ∈ U)
    (hU' : ∀ h ∈ U, g⁻¹ * h * g⁻¹⁻¹ ∈ U) : g ∈ Subgroup.normalizer (U : Set P8) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hU h
  · intro hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    have := hU' _ hh
    rwa [e] at this

theorem nor_Ub_of (g : P8)
    (hg : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, ∃ t', g * tup4 qa qb qc qd t * g⁻¹ = tup4 qa qb qc qd t') :
    ∀ h ∈ Ub, g * h * g⁻¹ ∈ Ub := by
  intro h hh
  obtain ⟨t, rfl⟩ := (mem_Ub_iff h).1 hh
  obtain ⟨t', ht'⟩ := hg t
  rw [mem_Ub_iff, ht']
  exact ⟨t', rfl⟩

theorem nor_Ua_of (g : P8)
    (hg : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, ∃ t', g * tup4 pa pb pc pd t * g⁻¹ = tup4 pa pb pc pd t') :
    ∀ h ∈ Ua, g * h * g⁻¹ ∈ Ua := by
  intro h hh
  obtain ⟨t, rfl⟩ := (mem_Ua_iff h).1 hh
  obtain ⟨t', ht'⟩ := hg t
  rw [mem_Ua_iff, ht']
  exact ⟨t', rfl⟩

theorem cc_tUb : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    ∃ t', cc * tup4 qa qb qc qd t * cc⁻¹ = tup4 qa qb qc qd t' := by decide +kernel
theorem cci_tUb : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    ∃ t', cc⁻¹ * tup4 qa qb qc qd t * cc⁻¹⁻¹ = tup4 qa qb qc qd t' := by decide +kernel
theorem dd_tUb : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    ∃ t', dd * tup4 qa qb qc qd t * dd⁻¹ = tup4 qa qb qc qd t' := by decide +kernel
theorem ddi_tUb : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    ∃ t', dd⁻¹ * tup4 qa qb qc qd t * dd⁻¹⁻¹ = tup4 qa qb qc qd t' := by decide +kernel
theorem cc_tUa : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    ∃ t', cc * tup4 pa pb pc pd t * cc⁻¹ = tup4 pa pb pc pd t' := by decide +kernel
theorem cci_tUa : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    ∃ t', cc⁻¹ * tup4 pa pb pc pd t * cc⁻¹⁻¹ = tup4 pa pb pc pd t' := by decide +kernel
theorem dd_tUa : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    ∃ t', dd * tup4 pa pb pc pd t * dd⁻¹ = tup4 pa pb pc pd t' := by decide +kernel
theorem ddi_tUa : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    ∃ t', dd⁻¹ * tup4 pa pb pc pd t * dd⁻¹⁻¹ = tup4 pa pb pc pd t' := by decide +kernel

theorem Ub_nor_cc : cc ∈ Subgroup.normalizer (Ub : Set P8) :=
  nor_of_gens (nor_Ub_of cc cc_tUb) (nor_Ub_of cc⁻¹ cci_tUb)
theorem Ub_nor_dd : dd ∈ Subgroup.normalizer (Ub : Set P8) :=
  nor_of_gens (nor_Ub_of dd dd_tUb) (nor_Ub_of dd⁻¹ ddi_tUb)
theorem Ua_nor_cc : cc ∈ Subgroup.normalizer (Ua : Set P8) :=
  nor_of_gens (nor_Ua_of cc cc_tUa) (nor_Ua_of cc⁻¹ cci_tUa)
theorem Ua_nor_dd : dd ∈ Subgroup.normalizer (Ua : Set P8) :=
  nor_of_gens (nor_Ua_of dd dd_tUa) (nor_Ua_of dd⁻¹ ddi_tUa)

theorem Eo_le_nor {U : Subgroup P8} (hc : cc ∈ Subgroup.normalizer (U : Set P8))
    (hd : dd ∈ Subgroup.normalizer (U : Set P8)) : Eo ≤ Subgroup.normalizer (U : Set P8) := by
  show Subgroup.closure ({m₁, m₂} : Set P8) ≤ Subgroup.normalizer (U : Set P8)
  refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩)
  · rw [m1_eq]; exact mul_mem hc hd
  · rw [m2_eq]; exact mul_mem hc (mul_mem hd hd)

theorem Ub_eq_def : Ub = v4 3 4 5 7 ⊔ v4 0 1 2 6 := rfl
theorem Ua_eq_def : Ua = v4 3 4 5 6 ⊔ v4 0 1 2 7 := rfl

theorem U1_eq_Ub : U₁ = Ub := by
  rw [Ub_eq_def]
  apply le_antisymm
  · unfold U₁
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (v4_gen1 0 1 2 6)
    · exact Subgroup.mem_sup_right (v4_gen2 0 1 2 6)
    · exact Subgroup.mem_sup_left (v4_gen1 3 4 5 7)
    · exact Subgroup.mem_sup_left (v4_gen2 3 4 5 7)
  · refine sup_le (v4_closure_le 3 4 5 7 U₁ ?_ ?_) (v4_closure_le 0 1 2 6 U₁ ?_ ?_)
    · exact Subgroup.subset_closure (by simp [U₁])
    · exact Subgroup.subset_closure (by simp [U₁])
    · exact Subgroup.subset_closure (by simp [U₁])
    · exact Subgroup.subset_closure (by simp [U₁])

theorem U2_eq_Ua : U₂ = Ua := by
  rw [Ua_eq_def]
  apply le_antisymm
  · unfold U₂
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (v4_gen1 0 1 2 7)
    · exact Subgroup.mem_sup_right (v4_gen2 0 1 2 7)
    · exact Subgroup.mem_sup_left (v4_gen1 3 4 5 6)
    · exact Subgroup.mem_sup_left (v4_gen2 3 4 5 6)
  · refine sup_le (v4_closure_le 3 4 5 6 U₂ ?_ ?_) (v4_closure_le 0 1 2 7 U₂ ?_ ?_)
    · exact Subgroup.subset_closure (by simp [U₂])
    · exact Subgroup.subset_closure (by simp [U₂])
    · exact Subgroup.subset_closure (by simp [U₂])
    · exact Subgroup.subset_closure (by simp [U₂])

theorem tau_V3457 : (v4 3 4 5 7).map (MulAut.conj τ₀).toMonoidHom = v4 3 4 5 6 := by
  have e1 : (MulAut.conj τ₀).toMonoidHom (swap 3 4 * swap 5 7) = swap 3 4 * swap 5 6 := by decide
  have e2 : (MulAut.conj τ₀).toMonoidHom (swap 3 5 * swap 4 7) = swap 3 5 * swap 4 6 := by decide
  unfold v4
  rw [MonoidHom.map_closure, Set.image_pair, e1, e2]

theorem tau_V0126 : (v4 0 1 2 6).map (MulAut.conj τ₀).toMonoidHom = v4 0 1 2 7 := by
  have e1 : (MulAut.conj τ₀).toMonoidHom (swap 0 1 * swap 2 6) = swap 0 1 * swap 2 7 := by decide
  have e2 : (MulAut.conj τ₀).toMonoidHom (swap 0 2 * swap 1 6) = swap 0 2 * swap 1 7 := by decide
  unfold v4
  rw [MonoidHom.map_closure, Set.image_pair, e1, e2]

theorem conj_U1 : conjBy τ₀ U₁ = U₂ := by
  rw [U1_eq_Ub, U2_eq_Ua, Ub_eq_def, Ua_eq_def]
  unfold CFSG.RankThree.PartTwo.Sec21.FF79.conjBy
  rw [Subgroup.map_sup, tau_V3457, tau_V0126]

set_option maxRecDepth 100000 in
theorem Y_sup (Y : Subgroup P8) (hY2 : IsPGroup 2 Y) (hEY : Eo ≤ Subgroup.normalizer (Y : Set P8))
    (hm1 : Y ⊓ Subgroup.centralizer ({cc * dd} : Set P8) = ⊥)
    (hm2 : Y ⊓ Subgroup.centralizer ({cc * (dd * dd)} : Set P8) = ⊥) :
    Y ≤ (Y ⊓ Subgroup.centralizer ({cc} : Set P8)) ⊔ (Y ⊓ Subgroup.centralizer ({dd} : Set P8)) := by
  have hgen := B_gen_centralizers Eo_card9 hY2 hEY
  refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
  have hS := Eo_mem ha
  simp only [Slist, List.mem_cons, List.mem_nil_iff, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl ha1
  · exact le_sup_left
  · exact (sub_of_sq Y (x := cc) (y := cc * cc) (by decide)).trans le_sup_left
  · exact le_sup_right
  · exact (sub_of_sq Y (x := dd) (y := dd * dd) (by decide)).trans le_sup_right
  · rw [hm1]; exact bot_le
  · rw [hm2]; exact bot_le
  · have h := sub_of_sq Y (x := cc * (dd * dd)) (y := cc * cc * dd) (by decide)
    rw [hm2] at h
    exact h.trans bot_le
  · have h := sub_of_sq Y (x := cc * dd) (y := cc * cc * (dd * dd)) (by decide)
    rw [hm1] at h
    exact h.trans bot_le

theorem core_Y (Y : Subgroup P8) (hYA : Y ≤ A8s) (hY2 : IsPGroup 2 Y)
    (hEY : Eo ≤ Subgroup.normalizer (Y : Set P8)) : Y ≤ Ub ∨ Y ≤ Ua := by
  have hcc : cc ∈ Subgroup.normalizer (Y : Set P8) := hEY cc_mem_Eo
  have hdd : dd ∈ Subgroup.normalizer (Y : Set P8) := hEY dd_mem_Eo
  have hm1 : Y ⊓ Subgroup.centralizer ({cc * dd} : Set P8) = ⊥ :=
    R_bot hYA hY2 hcc hdd (by decide) (by decide)
      (card_dvd_two Y hYA hY2 _ card_cent_m1 (Subgroup.mem_centralizer_singleton_iff.2 (by decide)))
  have hm2 : Y ⊓ Subgroup.centralizer ({cc * (dd * dd)} : Set P8) = ⊥ :=
    R_bot hYA hY2 hcc hdd (by decide) (by decide)
      (card_dvd_two Y hYA hY2 _ card_cent_m2 (Subgroup.mem_centralizer_singleton_iff.2 (by decide)))
  have hsup := Y_sup Y hY2 hEY hm1 hm2
  have hA1 : Y ⊓ Subgroup.centralizer ({cc} : Set P8) ≤ A8s := inf_le_left.trans hYA
  have hA2 : Y ⊓ Subgroup.centralizer ({dd} : Set P8) ≤ A8s := inf_le_left.trans hYA
  have hP1 : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer ({cc} : Set P8)) := hY2.to_inf_left
  have hP2 : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer ({dd} : Set P8)) := hY2.to_inf_left
  have hfix1 : ∀ g ∈ Y ⊓ Subgroup.centralizer ({cc} : Set P8), g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2 := by
    intro g hg
    obtain ⟨hgY, hgC⟩ := Subgroup.mem_inf.1 hg
    exact fix012_of_cent_cc g (Subgroup.mem_centralizer_singleton_iff.1 hgC) (pow2_of_mem hY2 hgY)
  have hfix2 : ∀ g ∈ Y ⊓ Subgroup.centralizer ({dd} : Set P8), g 3 = 3 ∧ g 4 = 4 ∧ g 5 = 5 := by
    intro g hg
    obtain ⟨hgY, hgC⟩ := Subgroup.mem_inf.1 hg
    exact fix345_of_cent_dd g (Subgroup.mem_centralizer_singleton_iff.1 hgC) (pow2_of_mem hY2 hgY)
  have hdd1 : ∀ g ∈ Y ⊓ Subgroup.centralizer ({cc} : Set P8),
      dd * g * dd⁻¹ ∈ Y ⊓ Subgroup.centralizer ({cc} : Set P8) := by
    intro g hg
    obtain ⟨hgY, hgC⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hdd g).1 hgY, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact conj_cent (show Commute dd cc from (by decide : dd * cc = cc * dd))
      (show Commute g cc from Subgroup.mem_centralizer_singleton_iff.1 hgC)
  have hcc2 : ∀ g ∈ Y ⊓ Subgroup.centralizer ({dd} : Set P8),
      cc * g * cc⁻¹ ∈ Y ⊓ Subgroup.centralizer ({dd} : Set P8) := by
    intro g hg
    obtain ⟨hgY, hgC⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hcc g).1 hgY, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact conj_cent (show Commute cc dd from (by decide : cc * dd = dd * cc))
      (show Commute g dd from Subgroup.mem_centralizer_singleton_iff.1 hgC)
  have hQ1 := T1 _ hA1 hP1 hfix1 hdd1
  have hQ2 := T2 _ hA2 hP2 hfix2 hcc2
  rcases hQ1 with h1 | h1 | h1 <;> rcases hQ2 with h2 | h2 | h2 <;> rw [h1, h2] at hsup
  · exact Or.inl (hsup.trans ((sup_le bot_le bot_le).trans bot_le))
  · exact Or.inl (hsup.trans (sup_le bot_le le_sup_right))
  · exact Or.inr (hsup.trans (sup_le bot_le le_sup_right))
  · exact Or.inr (hsup.trans (sup_le le_sup_left bot_le))
  · exfalso
    have hu : swap 3 4 * swap 5 6 ∈ Y ⊓ Subgroup.centralizer ({cc} : Set P8) := by
      rw [h1]; exact v4_gen1 3 4 5 6
    have hv : swap 0 1 * swap 2 6 ∈ Y ⊓ Subgroup.centralizer ({dd} : Set P8) := by
      rw [h2]; exact v4_gen1 0 1 2 6
    exact no_order3 hY2
      (mul_mem (mul_mem (Subgroup.mem_inf.1 hu).1 (Subgroup.mem_inf.1 hv).1)
        (mul_mem (Subgroup.mem_inf.1 hu).1 (Subgroup.mem_inf.1 hv).1)) (by decide) (by decide)
  · exact Or.inr (hsup.trans (sup_le le_sup_left le_sup_right))
  · exact Or.inl (hsup.trans (sup_le le_sup_left bot_le))
  · exact Or.inl (hsup.trans (sup_le le_sup_left le_sup_right))
  · exfalso
    have hu : swap 3 4 * swap 5 7 ∈ Y ⊓ Subgroup.centralizer ({cc} : Set P8) := by
      rw [h1]; exact v4_gen1 3 4 5 7
    have hv : swap 0 1 * swap 2 7 ∈ Y ⊓ Subgroup.centralizer ({dd} : Set P8) := by
      rw [h2]; exact v4_gen1 0 1 2 7
    exact no_order3 hY2
      (mul_mem (mul_mem (Subgroup.mem_inf.1 hu).1 (Subgroup.mem_inf.1 hv).1)
        (mul_mem (Subgroup.mem_inf.1 hu).1 (Subgroup.mem_inf.1 hv).1)) (by decide) (by decide)

theorem A10_maxE0 :
    (IsElemAb 2 4 U₁ ∧ IsElemAb 2 4 U₂ ∧ U₁ ⊓ U₂ = ⊥ ∧ Eo ≤ Nor U₁ ∧ Eo ≤ Nor U₂ ∧
      conjBy τ₀ U₁ = U₂) ∧
    ∀ Y : Subgroup P8, Y ≤ A8s → IsPGroup 2 Y → Eo ≤ Nor Y → Y ≤ U₁ ∨ Y ≤ U₂ := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, conj_U1⟩, fun Y hYA hY2 hEY => ?_⟩
  · unfold IsElemAb
    rw [U1_eq_Ub]
    exact ⟨Ub_isEA, by rw [Ub_card]; norm_num⟩
  · unfold IsElemAb
    rw [U2_eq_Ua]
    exact ⟨Ua_isEA, by rw [Ua_card]; norm_num⟩
  · rw [U1_eq_Ub, U2_eq_Ua]
    exact (inf_comm _ _).trans Ua_inf_Ub
  · rw [U1_eq_Ub]
    exact Eo_le_nor Ub_nor_cc Ub_nor_dd
  · rw [U2_eq_Ua]
    exact Eo_le_nor Ua_nor_cc Ua_nor_dd
  · rcases core_Y Y hYA hY2 hEY with h | h
    · exact Or.inl (by rw [U1_eq_Ub]; exact h)
    · exact Or.inr (by rw [U2_eq_Ua]; exact h)

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
