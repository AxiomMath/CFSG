module

public import CFSG.Quasithin.Background.C124YZSwap
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YZ

open Equiv Equiv.Perm

variable {Ω : Type*} [DecidableEq Ω]

section Generation

variable [Fintype Ω]

theorem eq_top_of_swap_mem (K : Subgroup (Perm Ω)) (c : Ω) (hK : ∀ x, x ≠ c → swap x c ∈ K) :
    K = ⊤ := by
  rw [eq_top_iff, ← closure_isSwap, Subgroup.closure_le]
  rintro _ ⟨x, y, hxy, rfl⟩
  by_cases hx : x = c
  · subst hx
    rw [swap_comm]
    exact hK y (Ne.symm hxy)
  by_cases hy : y = c
  · subst hy
    exact hK x hx
  have h : swap x y = swap x c * swap y c * swap x c := by
    have h1 := swap_apply_apply (swap x c) y c
    rw [swap_apply_of_ne_of_ne (Ne.symm hxy) hy, swap_apply_right, swap_inv] at h1
    exact (swap_comm x y).trans h1
  rw [h]
  exact K.mul_mem (K.mul_mem (hK x hx) (hK y hy)) (hK x hx)

section Normalizer

variable {H : Subgroup (Perm Ω)}

theorem eq_swap_of_meets (hp : IsPGroup 2 H) {u v p q : Ω} (huv : u ≠ v) (hpq : p ≠ q)
    (h1 : swap u v ∈ H) (h : swap p q ∈ H) (hm : p = u ∨ p = v ∨ q = u ∨ q = v) :
    (p = u ∧ q = v) ∨ (p = v ∧ q = u) := by
  have key : ∀ {s t r : Ω}, s ≠ t → s ≠ r → swap s t ∈ H → swap s r ∈ H → t = r :=
    fun hst hsr h1 h2 => eq_of_swap_mem_swap_mem hp hst hsr h1 h2
  have h1' : swap v u ∈ H := by rwa [swap_comm]
  have h' : swap q p ∈ H := by rwa [swap_comm]
  rcases hm with hm | hm | hm | hm
  · rw [hm] at h hpq
    exact Or.inl ⟨hm, (key huv hpq h1 h).symm⟩
  · rw [hm] at h hpq
    exact Or.inr ⟨hm, (key (Ne.symm huv) hpq h1' h).symm⟩
  · rw [hm] at h' hpq
    exact Or.inr ⟨(key huv (Ne.symm hpq) h1 h').symm, hm⟩
  · rw [hm] at h' hpq
    exact Or.inl ⟨(key (Ne.symm huv) (Ne.symm hpq) h1' h').symm, hm⟩

theorem swap_mem_cases (hp : IsPGroup 2 H) {a b x y p q : Ω} (hab : a ≠ b) (hxy : x ≠ y)
    (hpq : p ≠ q) (h1 : swap a b ∈ H) (h2 : swap x y ∈ H) (h : swap p q ∈ H) :
    ((p = a ∧ q = b) ∨ (p = b ∧ q = a)) ∨ ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) ∨
      (p ≠ a ∧ p ≠ b ∧ p ≠ x ∧ p ≠ y ∧ q ≠ a ∧ q ≠ b ∧ q ≠ x ∧ q ≠ y) := by
  by_cases hm : p = a ∨ p = b ∨ q = a ∨ q = b
  · exact Or.inl (eq_swap_of_meets hp hab hpq h1 h hm)
  by_cases hm' : p = x ∨ p = y ∨ q = x ∨ q = y
  · exact Or.inr (Or.inl (eq_swap_of_meets hp hxy hpq h2 h hm'))
  right
  right
  push Not at hm hm'
  exact ⟨hm.1, hm.2.1, hm'.1, hm'.2.1, hm.2.2.1, hm.2.2.2, hm'.2.2.1, hm'.2.2.2⟩

theorem mem_normalizer_swap_mul_swap (hH : IsSwapGroup H) (hp : IsPGroup 2 H) {a b x y : Ω}
    (hab : a ≠ b) (hxy : x ≠ y) (hay : a ≠ y) (hbx : b ≠ x)
    (h1 : swap a b ∈ H) (h2 : swap x y ∈ H) :
    swap a x * swap b y ∈ Subgroup.normalizer (H : Set (Perm Ω)) := by
  set n : Perm Ω := swap a x * swap b y with hn
  have hna : n a = x := by
    rw [hn, Perm.mul_apply, swap_apply_of_ne_of_ne hab hay, swap_apply_left]
  have hnb : n b = y := by
    rw [hn, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hay) (Ne.symm hxy)]
  have hnx : n x = a := by
    rw [hn, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hbx) hxy, swap_apply_right]
  have hny : n y = b := by
    rw [hn, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hab) hbx]
  have hnp : ∀ p, p ≠ a → p ≠ b → p ≠ x → p ≠ y → n p = p := by
    intro p h1 h2 h3 h4
    rw [hn, Perm.mul_apply, swap_apply_of_ne_of_ne h2 h4, swap_apply_of_ne_of_ne h1 h3]
  have hconj : ∀ p q, p ≠ q → swap p q ∈ H → n * swap p q * n⁻¹ ∈ H := by
    intro p q hpq h
    rw [← swap_apply_apply]
    rcases swap_mem_cases hp hab hxy hpq h1 h2 h with (⟨e1, e2⟩ | ⟨e1, e2⟩) |
      (⟨e1, e2⟩ | ⟨e1, e2⟩) | ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩
    · rw [e1, e2, hna, hnb]; exact h2
    · rw [e1, e2, hna, hnb, swap_comm]; exact h2
    · rw [e1, e2, hnx, hny]; exact h1
    · rw [e1, e2, hnx, hny, swap_comm]; exact h1
    · rw [hnp p e1 e2 e3 e4, hnp q e5 e6 e7 e8]
      exact h
  refine Subgroup.mem_normalizer_fintype fun σ hσ => ?_
  have hσH : σ ∈ H := hσ
  show n * σ * n⁻¹ ∈ H
  refine hH.mem_of _ fun z => ?_
  by_cases hw : σ (n⁻¹ z) = n⁻¹ z
  · left
    rw [Perm.mul_apply, Perm.mul_apply, hw]
    exact n.apply_symm_apply z
  · right
    have ht := (hH σ hσH (n⁻¹ z)).resolve_left hw
    have := hconj _ _ (fun e => hw e.symm) ht
    rw [← swap_apply_apply] at this
    simpa [Perm.mul_apply] using this

end Normalizer

section ThreeCycle

theorem swap_mul_swap_eq_inv {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    swap b a * swap b c = (swap a b * swap a c)⁻¹ := by
  rw [mul_inv_rev, swap_inv, swap_inv]
  ext z
  simp only [Perm.mul_apply, swap_apply_def]
  by_cases h1 : z = a <;> by_cases h2 : z = b <;> by_cases h3 : z = c <;>
    simp [h1, h2, h3, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]

theorem conj_threeCycle_mem {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {σ : Perm Ω}
    (ha : σ a = a ∨ σ a = b) (hb : σ b = a ∨ σ b = b) (hc : σ c = c) :
    σ * (swap a b * swap a c) * σ⁻¹ ∈ Subgroup.zpowers (swap a b * swap a c) := by
  have h : σ * (swap a b * swap a c) * σ⁻¹ =
      swap (σ a) (σ b) * swap (σ a) c := by
    have e1 := swap_apply_apply σ a b
    have e2 := swap_apply_apply σ a c
    rw [hc] at e2
    rw [e1, e2]
    group
  rcases ha with ha | ha
  · have hb' : σ b = b := by
      rcases hb with hb | hb
      · exact absurd (σ.injective (ha.trans hb.symm)) hab
      · exact hb
    rw [h, ha, hb']
    exact Subgroup.mem_zpowers _
  · have hb' : σ b = a := by
      rcases hb with hb | hb
      · exact hb
      · exact absurd (σ.injective (ha.trans hb.symm)) hab
    rw [h, ha, hb', swap_mul_swap_eq_inv hab hac hbc]
    exact inv_mem (Subgroup.mem_zpowers _)

end ThreeCycle

theorem zpowers_sup_normalizer_eq_top {H : Subgroup (Perm Ω)} (hH : IsSwapGroup H)
    (hp : IsPGroup 2 H) {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : swap a b ∈ H) (hc : ∀ d ∈ H, d c = c) :
    Subgroup.zpowers (swap a b * swap a c) ⊔ Subgroup.normalizer (H : Set (Perm Ω)) = ⊤ := by
  set K := Subgroup.zpowers (swap a b * swap a c) ⊔ Subgroup.normalizer (H : Set (Perm Ω))
    with hK
  have hHK : H ≤ K := Subgroup.le_normalizer.trans le_sup_right
  have hy3 : swap a b * swap a c ∈ K := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hbcK : swap b c ∈ K := by
    have e := swap_apply_apply (swap a b) a c
    rw [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc), swap_inv] at e
    rw [e]
    exact K.mul_mem hy3 (hHK h)
  have hacK : swap a c ∈ K := by
    have e := swap_apply_apply (swap a b) b c
    rw [swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc), swap_inv] at e
    rw [e]
    exact K.mul_mem (K.mul_mem (hHK h) hbcK) (hHK h)
  refine eq_top_of_swap_mem K c fun x hx => ?_
  by_cases hxa : x = a
  · rw [hxa]
    exact hacK
  by_cases hxb : x = b
  · rw [hxb]
    exact hbcK
  by_cases hfix : ∀ d ∈ H, d x = x
  · refine Subgroup.mem_sup_right (Subgroup.mem_normalizer_fintype fun d hd => ?_)
    have hdH : d ∈ H := hd
    have e := swap_apply_apply d x c
    rw [hfix d hdH, hc d hdH] at e
    have e2 : swap x c * d * (swap x c)⁻¹ = d := by
      have : swap x c * d = d * swap x c := by
        have := congrArg (fun t => t * d) e
        simp only [mul_assoc, inv_mul_cancel, mul_one] at this
        simpa [mul_assoc] using this
      rw [this]
      group
    rw [e2]
    exact hdH
  · push Not at hfix
    obtain ⟨d, hd, hdx⟩ := hfix
    have hxx' : swap x (d x) ∈ H := (hH d hd x).resolve_left hdx
    have hx'a : d x ≠ a := by
      intro e
      rw [e, swap_comm] at hxx'
      exact hxb (eq_of_swap_mem_swap_mem hp hab (Ne.symm hxa) h hxx').symm
    have hx'b : d x ≠ b := by
      intro e
      rw [e, swap_comm] at hxx'
      have h' : swap b a ∈ H := by rwa [swap_comm]
      exact hxa (eq_of_swap_mem_swap_mem hp (Ne.symm hab) (Ne.symm hxb) h' hxx').symm
    have hx'c : d x ≠ c := by
      intro e
      exact hx (d.injective (e.trans (hc d hd).symm))
    have hn := mem_normalizer_swap_mul_swap hH hp hab hdx.symm hx'a.symm (Ne.symm hxb) h hxx'
    have hnK : swap a x * swap b (d x) ∈ K := Subgroup.mem_sup_right hn
    have hna : (swap a x * swap b (d x)) a = x := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab hx'a.symm, swap_apply_left]
    have hnc : (swap a x * swap b (d x)) c = c := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hbc) (Ne.symm hx'c),
        swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hx)]
    have e := swap_apply_apply (swap a x * swap b (d x)) a c
    rw [hna, hnc] at e
    rw [e]
    exact K.mul_mem (K.mul_mem hnK hacK) (K.inv_mem hnK)

end Generation

end CFSG.Quasithin.C124.YZ
