module

public import CFSG.Sporadic.Recognition.LyonsAS4Perm
public import CFSG.Sporadic.Recognition.LyonsAS4Embed

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

theorem x1p_apply_ne_iff (x : Fin 11) : x1p x ≠ x ↔ x.val < 3 := by
  revert x
  decide

theorem lt_three_apply_iff_of_normalizes {σ : Perm (Fin 11)}
    (hσ : σ * x1p * σ⁻¹ = x1p ∨ σ * x1p * σ⁻¹ = x1p⁻¹) (x : Fin 11) :
    (σ x).val < 3 ↔ x.val < 3 := by
  have hconj : ∀ y, (σ * x1p * σ⁻¹) (σ y) = σ (x1p y) := fun y => by simp
  rw [← x1p_apply_ne_iff, ← x1p_apply_ne_iff]
  rcases hσ with h | h
  · rw [h] at hconj
    rw [hconj x]
    exact σ.injective.ne_iff
  · rw [h] at hconj
    have e : x1p⁻¹ (σ x) = σ x ↔ x1p x = x := by
      rw [hconj x]
      exact σ.injective.eq_iff
    rw [Perm.inv_eq_iff_eq] at e
    exact not_congr (eq_comm.trans e)

theorem conj_mem_fix012_of_normalizes {σ τ : Perm (Fin 11)}
    (hσ : σ * x1p * σ⁻¹ = x1p ∨ σ * x1p * σ⁻¹ = x1p⁻¹) (hτ : τ ∈ fix012) :
    σ * τ * σ⁻¹ ∈ fix012 := by
  have hfix : ∀ j : Fin 11, j.val < 3 → (σ * τ * σ⁻¹) j = j := by
    intro j hj
    have h1 : (σ⁻¹ j).val < 3 :=
      (lt_three_apply_iff_of_normalizes hσ (σ⁻¹ j)).1 (by simpa using hj)
    have h2 : τ (σ⁻¹ j) = σ⁻¹ j := fix012_apply_of_lt hτ h1
    rw [Perm.mul_apply, Perm.mul_apply, h2]
    exact σ.apply_symm_apply j
  exact ⟨hfix 0 (by decide), hfix 1 (by decide), hfix 2 (by decide)⟩

theorem apply_mem_of_commute_all {σ : Perm (Fin 11)}
    (h : ∀ τ ∈ fix012 ⊓ alternatingGroup (Fin 11), σ * τ = τ * σ) {i j k : Fin 11}
    (hi : 3 ≤ i.val) (hj : 3 ≤ j.val) (hk : 3 ≤ k.val) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : σ i = i ∨ σ i = j ∨ σ i = k := by
  obtain ⟨c, hc⟩ : ∃ c : Perm (Fin 11), c = swap i k * swap i j := ⟨_, rfl⟩
  have hci : c i = j := by
    rw [hc, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hij.symm hjk]
  have hcx : ∀ x : Fin 11, x ≠ i → x ≠ j → x ≠ k → c x = x := fun x hxi hxj hxk => by
    rw [hc, Perm.mul_apply, swap_apply_of_ne_of_ne hxi hxj, swap_apply_of_ne_of_ne hxi hxk]
  have hmem : c ∈ fix012 ⊓ alternatingGroup (Fin 11) := by
    have hfix : ∀ x : Fin 11, x.val < 3 → c x = x := fun x hx =>
      hcx x (fun e => by rw [e] at hx; omega) (fun e => by rw [e] at hx; omega)
        (fun e => by rw [e] at hx; omega)
    refine ⟨⟨hfix 0 (by decide), hfix 1 (by decide), hfix 2 (by decide)⟩,
      mem_alternatingGroup.2 ?_⟩
    rw [hc, map_mul, sign_swap hik, sign_swap hij]
    rfl
  have hcomm : σ j = c (σ i) := by
    rw [← hci]
    exact DFunLike.congr_fun (h c hmem) i
  by_cases h1 : σ i = i
  · exact Or.inl h1
  by_cases h2 : σ i = j
  · exact Or.inr (Or.inl h2)
  by_cases h3 : σ i = k
  · exact Or.inr (Or.inr h3)
  rw [hcx (σ i) h1 h2 h3] at hcomm
  exact absurd (σ.injective hcomm).symm hij

theorem fix_of_commute_all {σ : Perm (Fin 11)}
    (h : ∀ τ ∈ fix012 ⊓ alternatingGroup (Fin 11), σ * τ = τ * σ) {i : Fin 11}
    (hi : 3 ≤ i.val) : σ i = i := by
  have key : ∀ a b c d e : Fin 11,
      (3 ≤ a.val ∧ 3 ≤ b.val ∧ 3 ≤ c.val ∧ 3 ≤ d.val ∧ 3 ≤ e.val) ∧
      (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ d ∧ a ≠ e ∧ d ≠ e ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e) →
      σ a = a := by
    rintro a b c d e ⟨⟨ha, hb, hc, hd, he⟩, hab, hac, hbc, had, hae, hde, hbd, hbe, hcd, hce⟩
    rcases apply_mem_of_commute_all h ha hb hc hab hac hbc with h1 | h1 | h1
    · exact h1
    · rcases apply_mem_of_commute_all h ha hd he had hae hde with h2 | h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hbd
      · exact absurd (h1.symm.trans h2) hbe
    · rcases apply_mem_of_commute_all h ha hd he had hae hde with h2 | h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hcd
      · exact absurd (h1.symm.trans h2) hce
  have hcases : ∀ i : Fin 11, 3 ≤ i.val →
      i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by
    decide
  rcases hcases i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key 3 4 5 6 7 (by decide)
  · exact key 4 3 5 6 7 (by decide)
  · exact key 5 3 4 6 7 (by decide)
  · exact key 6 3 4 5 7 (by decide)
  · exact key 7 3 4 5 6 (by decide)
  · exact key 8 3 4 5 6 (by decide)
  · exact key 9 3 4 5 6 (by decide)
  · exact key 10 3 4 5 6 (by decide)

theorem triple_cases (a b c : Fin 11) (ha : a.val < 3) (hb : b.val < 3) (hc : c.val < 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) ∨
      (a = 1 ∧ b = 0 ∧ c = 2) ∨ (a = 2 ∧ b = 1 ∧ c = 0) ∨ (a = 0 ∧ b = 2 ∧ c = 1) := by
  have h3 : ∀ x : Fin 11, x.val < 3 → x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases h3 a ha with rfl | rfl | rfl <;> rcases h3 b hb with rfl | rfl | rfl <;>
    rcases h3 c hc with rfl | rfl | rfl <;> revert hab hac hbc <;> decide

theorem eq_pow_x1p_of_fix_of_even {σ : Perm (Fin 11)}
    (h : ∀ i : Fin 11, 3 ≤ i.val → σ i = i) (hs : sign σ = 1) :
    σ = 1 ∨ σ = x1p ∨ σ = x1p ^ 2 := by
  have hlt : ∀ j : Fin 11, j.val < 3 → (σ j).val < 3 := by
    intro j hj
    by_contra hge
    have h2 : σ j = j := σ.injective (h (σ j) (by omega))
    rw [h2] at hge
    omega
  have hext : ∀ τ : Perm (Fin 11), (∀ i : Fin 11, 3 ≤ i.val → τ i = i) →
      σ 0 = τ 0 → σ 1 = τ 1 → σ 2 = τ 2 → σ = τ := by
    intro τ hτ h0 h1 h2
    refine Perm.ext fun i => ?_
    by_cases hi : 3 ≤ i.val
    · rw [h i hi, hτ i hi]
    · have hlt3 : ∀ i : Fin 11, i.val < 3 → i = 0 ∨ i = 1 ∨ i = 2 := by decide
      rcases hlt3 i (by omega) with rfl | rfl | rfl <;> assumption
  have hdist : ∀ a b : Fin 11, a ≠ b → σ a ≠ σ b := fun a b hab e => hab (σ.injective e)
  rcases triple_cases (σ 0) (σ 1) (σ 2) (hlt 0 (by decide)) (hlt 1 (by decide))
      (hlt 2 (by decide)) (hdist 0 1 (by decide)) (hdist 0 2 (by decide))
      (hdist 1 2 (by decide)) with
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact Or.inl (hext 1 (by decide) (by rw [h0]; decide) (by rw [h1]; decide)
      (by rw [h2]; decide))
  · exact Or.inr (Or.inl (hext x1p (by decide) (by rw [h0]; decide) (by rw [h1]; decide)
      (by rw [h2]; decide)))
  · exact Or.inr (Or.inr (hext (x1p ^ 2) (by decide) (by rw [h0]; decide) (by rw [h1]; decide)
      (by rw [h2]; decide)))
  · have hσ := hext (swap 0 1) (by decide) (by rw [h0]; decide) (by rw [h1]; decide)
      (by rw [h2]; decide)
    rw [hσ, sign_swap (by decide)] at hs
    exact absurd hs (by decide)
  · have hσ := hext (swap 0 2) (by decide) (by rw [h0]; decide) (by rw [h1]; decide)
      (by rw [h2]; decide)
    rw [hσ, sign_swap (by decide)] at hs
    exact absurd hs (by decide)
  · have hσ := hext (swap 1 2) (by decide) (by rw [h0]; decide) (by rw [h1]; decide)
      (by rw [h2]; decide)
    rw [hσ, sign_swap (by decide)] at hs
    exact absurd hs (by decide)

@[expose] def invP : Perm (Fin 11) := swap 1 2 * swap 3 4 * swap 5 6 * swap 7 8

theorem invP_sq : invP ^ 2 = 1 := by decide

theorem invP_support : invP.support.card = 8 := by decide

theorem invP_sign : sign invP = 1 := by decide

theorem invP_conj : invP * x1p * invP⁻¹ = x1p⁻¹ := by decide

end CFSG.Sporadic.Recognition.LyonsSims
