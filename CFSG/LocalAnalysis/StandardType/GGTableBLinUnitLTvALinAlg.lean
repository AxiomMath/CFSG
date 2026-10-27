module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.LinTvA

variable {p d : ℕ}

theorem exists_ne_four (hd : 5 ≤ d) (a b c e : Fin d) :
    ∃ i, i ≠ a ∧ i ≠ b ∧ i ≠ c ∧ i ≠ e := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, e} : Finset (Fin d))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact Finset.card_le_four.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  exact ⟨i, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2⟩

theorem exists_ne_two (hd : 3 ≤ d) (a b : Fin d) : ∃ i, i ≠ a ∧ i ≠ b := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b} : Finset (Fin d))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact Finset.card_le_two.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  exact ⟨i, hi.1, hi.2⟩

@[expose] def pairVec (p : ℕ) {d : ℕ} (a b : Fin d) : Fin d → ZMod p :=
  fun k => (if k = a then 1 else 0) - (if k = b then 1 else 0)

theorem pairVec_left {a b : Fin d} (hab : a ≠ b) : pairVec p a b a = 1 := by
  simp [pairVec, hab]

theorem pairVec_right {a b : Fin d} (hab : a ≠ b) : pairVec p a b b = -1 := by
  simp [pairVec, Ne.symm hab]

theorem pairVec_of_ne {a b k : Fin d} (hka : k ≠ a) (hkb : k ≠ b) : pairVec p a b k = 0 := by
  simp [pairVec, hka, hkb]

variable [Fact p.Prime]

theorem eq_one_of_pairVec (hd : 5 ≤ d) {c : ZMod p} {ρ : Equiv.Perm (Fin d)}
    (h : ∀ a b : Fin d, a ≠ b → ∀ k l,
      c * (pairVec p a b (ρ k) - pairVec p a b (ρ l)) = pairVec p a b k - pairVec p a b l) :
    c = 1 ∧ ρ = 1 := by
  have h1 : ∀ a b : Fin d, a ≠ b → ∀ k, c * pairVec p a b (ρ k) = pairVec p a b k := by
    intro a b hab k
    obtain ⟨m, hma, hmb, hmρa, hmρb⟩ := exists_ne_four hd a b (ρ.symm a) (ρ.symm b)
    have h2 := h a b hab k m
    have hv0 : pairVec p a b m = 0 := pairVec_of_ne hma hmb
    have hv1 : pairVec p a b (ρ m) = 0 := by
      apply pairVec_of_ne
      · intro h'
        apply hmρa
        rw [← h']
        simp
      · intro h'
        apply hmρb
        rw [← h']
        simp
    rw [hv0, hv1, sub_zero, sub_zero] at h2
    exact h2
  have hρ : ∀ a, ρ a = a := by
    intro a
    by_contra hρa
    obtain ⟨b₁, hb₁a, hb₁a'⟩ := exists_ne_two (by omega : 3 ≤ d) a a
    obtain ⟨b₂, hb₂a, hb₂b⟩ := exists_ne_two (by omega : 3 ≤ d) a b₁
    have hρb : ∀ b, b ≠ a → ρ a = b := by
      intro b hba
      by_contra hne
      have h3 := h1 a b (Ne.symm hba) a
      rw [pairVec_left (Ne.symm hba), pairVec_of_ne hρa hne, mul_zero] at h3
      exact zero_ne_one h3
    exact hb₂b (by rw [← hρb b₁ hb₁a, ← hρb b₂ hb₂a])
  have hρ1 : ρ = 1 := Equiv.ext fun a => by rw [hρ a]; rfl
  refine ⟨?_, hρ1⟩
  obtain ⟨b, hba, -⟩ := exists_ne_two (by omega : 3 ≤ d) ⟨0, by omega⟩ ⟨0, by omega⟩
  have h3 := h1 ⟨0, by omega⟩ b (Ne.symm hba) ⟨0, by omega⟩
  rw [hρ, pairVec_left (Ne.symm hba), mul_one] at h3
  exact h3

theorem apply_eq_of_sq_apply_eq {π : Equiv.Perm (Fin d)} (hp2 : p ≠ 2) (hπp : π ^ p = 1)
    {z : Fin d} (hz : π (π z) = z) : π z = z := by
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
  have h2 : (π ^ 2) z = z := by
    rw [pow_two, Equiv.Perm.mul_apply]
    exact hz
  have h3 : (π ^ (2 * m)) z = z := by
    rw [pow_mul]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h2 m
  have h4 : (π ^ p) z = z := by rw [hπp]; rfl
  rw [hm, pow_succ', Equiv.Perm.mul_apply, h3] at h4
  exact h4

theorem false_of_pairVec_transvection (hp2 : p ≠ 2) (hd : 5 ≤ d) {π : Equiv.Perm (Fin d)}
    (hπp : π ^ p = 1) (hπ : π ≠ 1)
    (h : ∀ a b : Fin d, a ≠ b → ∀ k l,
      pairVec p a b (π (π k)) - 2 * pairVec p a b (π k) + pairVec p a b k =
        pairVec p a b (π (π l)) - 2 * pairVec p a b (π l) + pairVec p a b l) : False := by
  obtain ⟨x, hx⟩ : ∃ x, π x ≠ x := by
    by_contra hcon
    exact hπ (Equiv.ext fun x => by_contra fun hx => hcon ⟨x, hx⟩)
  have hx2 : π (π x) ≠ x := fun h' => hx (apply_eq_of_sq_apply_eq hp2 hπp h')
  obtain ⟨y, hyx, hyπx, hyπ2x, hyπinv⟩ := exists_ne_four hd x (π x) (π (π x)) (π.symm x)
  have hxy : x ≠ y := Ne.symm hyx
  have h' := h x y hxy x y
  have hvx : pairVec p x y x = 1 := pairVec_left hxy
  have hvπx : pairVec p x y (π x) = 0 := pairVec_of_ne hx (Ne.symm hyπx)
  have hvπ2x : pairVec p x y (π (π x)) = 0 := pairVec_of_ne hx2 (Ne.symm hyπ2x)
  have hvy : pairVec p x y y = -1 := pairVec_right hxy
  have hπyx : π y ≠ x := fun h'' => hyπinv (by rw [← h'']; simp)
  rw [hvπ2x, hvπx, hvx, hvy] at h'
  by_cases hy1 : π y = y
  · have hvπy : pairVec p x y (π y) = -1 := by rw [hy1]; exact pairVec_right hxy
    have hvπ2y : pairVec p x y (π (π y)) = -1 := by
      rw [hy1, hy1]
      exact pairVec_right hxy
    rw [hvπy, hvπ2y] at h'
    have h3 : (1 : ZMod p) = 0 := by linear_combination h'
    exact one_ne_zero h3
  · have hy2 : π (π y) ≠ y := fun h'' => hy1 (apply_eq_of_sq_apply_eq hp2 hπp h'')
    have hvπy : pairVec p x y (π y) = 0 := pairVec_of_ne hπyx hy1
    rw [hvπy] at h'
    by_cases hyx2 : π (π y) = x
    · have hvπ2y : pairVec p x y (π (π y)) = 1 := by rw [hyx2]; exact pairVec_left hxy
      rw [hvπ2y] at h'
      have h3 : (1 : ZMod p) = 0 := by linear_combination h'
      exact one_ne_zero h3
    · have hvπ2y : pairVec p x y (π (π y)) = 0 := pairVec_of_ne hyx2 hy2
      rw [hvπ2y] at h'
      have h3 : (2 : ZMod p) = 0 := by linear_combination h'
      have h4 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
      rw [ZMod.natCast_eq_zero_iff] at h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h4)

end CFSG.StandardType.LinTvA

end
