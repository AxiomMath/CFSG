module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.ASVolI

section Dihedral

variable {G : Type*} [Group G]

@[expose] def burnsideF42g_Fix1 (X : Subgroup G) (c : G) : Prop :=
  ∀ k : G, k⁻¹ * c * k ∈ X → k ∈ X

theorem burnsideF42g_inv_self {a : G} (ha : a * a = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right ha

theorem burnsideF42g_dihedral_inv {a b : G} (ha : a * a = 1) (hb : b * b = 1) (j : ℕ) :
    a * (a * b) ^ j * a = ((a * b) ^ j)⁻¹ := by
  have ha' := burnsideF42g_inv_self ha
  have hb' := burnsideF42g_inv_self hb
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, hb', ha', ← mul_assoc, ha, one_mul]
  calc a * (a * b) ^ j * a = a * (a * b) ^ j * a⁻¹ := by rw [ha']
    _ = (a * (a * b) * a⁻¹) ^ j := (conj_pow).symm
    _ = ((a * b) ^ j)⁻¹ := by rw [h1, inv_pow]

theorem burnsideF42g_dihedral_conj {a b : G} (ha : a * a = 1) (hb : b * b = 1) (j : ℕ) :
    (a * b) ^ j * a * ((a * b) ^ j)⁻¹ = a * ((a * b) ^ (2 * j))⁻¹ := by
  have h := burnsideF42g_dihedral_inv ha hb j
  have h2 : (a * b) ^ j * a = a * ((a * b) ^ j)⁻¹ := by
    calc (a * b) ^ j * a = a * (a * (a * b) ^ j * a) := by
          rw [← mul_assoc, ← mul_assoc, ha, one_mul]
      _ = a * ((a * b) ^ j)⁻¹ := by rw [h]
  rw [h2, mul_assoc, ← mul_inv_rev, ← pow_add, two_mul]

theorem burnsideF42g_dihedral_odd {a b : G} (ha : a * a = 1) (hb : b * b = 1) {k : ℕ}
    (hn : orderOf (a * b) = 2 * k + 1) :
    (a * b) ^ k * a * ((a * b) ^ k)⁻¹ = b := by
  rw [burnsideF42g_dihedral_conj ha hb]
  have hc : (a * b) ^ (2 * k) * (a * b) = 1 := by
    rw [← pow_succ, ← hn, pow_orderOf_eq_one]
  have hc' : ((a * b) ^ (2 * k))⁻¹ = a * b := inv_eq_of_mul_eq_one_right hc
  rw [hc', ← mul_assoc, ha, one_mul]

theorem burnsideF42g_dihedral_even {a b : G} (ha : a * a = 1) (hb : b * b = 1) {m : ℕ}
    (hn : orderOf (a * b) = 2 * m) (hm : 0 < m) :
    (a * b) ^ m * (a * b) ^ m = 1 ∧ (a * b) ^ m ≠ 1 ∧ a * (a * b) ^ m = (a * b) ^ m * a ∧
      b * (a * b) ^ m = (a * b) ^ m * b := by
  have hw2 : (a * b) ^ m * (a * b) ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← hn, pow_orderOf_eq_one]
  have hwi : ((a * b) ^ m)⁻¹ = (a * b) ^ m := inv_eq_of_mul_eq_one_right hw2
  have hw1 : (a * b) ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hm.ne' (by omega)
  have hinv := burnsideF42g_dihedral_inv ha hb m
  rw [hwi] at hinv
  have haw : a * (a * b) ^ m = (a * b) ^ m * a := by
    calc a * (a * b) ^ m = a * (a * b) ^ m * a * a := by rw [mul_assoc _ a a, ha, mul_one]
      _ = (a * b) ^ m * a := by rw [hinv]
  refine ⟨hw2, hw1, haw, ?_⟩
  have hbac : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  calc b * (a * b) ^ m = a * (a * b) * (a * b) ^ m := by rw [hbac]
    _ = a * ((a * b) ^ m * (a * b)) := by rw [mul_assoc, (Commute.self_pow (a * b) m).eq]
    _ = (a * b) ^ m * (a * (a * b)) := by rw [← mul_assoc, haw, mul_assoc]
    _ = (a * b) ^ m * b := by rw [hbac]

theorem burnsideF42g_dihedral_four {a b : G} (ha : a * a = 1) (hb : b * b = 1) {p : ℕ}
    (hn : orderOf (a * b) = 2 * (2 * p)) (hp : 0 < p) :
    (a * b) ^ p * a * ((a * b) ^ p)⁻¹ = a * (a * b) ^ (2 * p) := by
  rw [burnsideF42g_dihedral_conj ha hb]
  obtain ⟨hw2, -, -, -⟩ := burnsideF42g_dihedral_even ha hb hn (by omega)
  rw [inv_eq_of_mul_eq_one_right hw2]

theorem burnsideF42g_dihedral_two {a b : G} (ha : a * a = 1) (hb : b * b = 1) {p : ℕ}
    (hn : orderOf (a * b) = 2 * (2 * p + 1)) :
    (a * b) ^ p * a * ((a * b) ^ p)⁻¹ = b * (a * b) ^ (2 * p + 1) := by
  rw [burnsideF42g_dihedral_conj ha hb]
  have hc : (a * b) ^ (2 * p) * ((a * b) ^ (2 * p + 1) * (a * b)) = 1 := by
    rw [← pow_succ, ← pow_add, show 2 * p + (2 * p + 1 + 1) = 2 * (2 * p + 1) by ring, ← hn,
      pow_orderOf_eq_one]
  have hbac : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  rw [inv_eq_of_mul_eq_one_right hc, ← pow_succ, pow_succ', ← mul_assoc, hbac]

end Dihedral

section LemmaB

variable {G : Type*} [Group G] [Finite G]

theorem burnsideF42g_order_cases (c : G) :
    (∃ k : ℕ, orderOf c = 2 * k + 1) ∨ ∃ m : ℕ, 0 < m ∧ orderOf c = 2 * m := by
  have hpos : 0 < orderOf c := orderOf_pos c
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (orderOf c)
  · exact Or.inr ⟨k, by omega, hk⟩
  · exact Or.inl ⟨k, hk⟩

omit [Finite G] in
theorem burnsideF42g_fix_of_comm {X : Subgroup G} {i k w a : G} (hiX : i ∈ X)
    (hfi : burnsideF42g_Fix1 X i) (hwk : w = k * i * k⁻¹) (haw : a * w = w * a) :
    k⁻¹ * a * k ∈ X := by
  apply hfi
  have e : (k⁻¹ * a * k)⁻¹ * i * (k⁻¹ * a * k) = k⁻¹ * (a⁻¹ * (w * a)) * k := by
    rw [hwk]; group
  rw [e, ← haw, inv_mul_cancel_left, hwk, show k⁻¹ * (k * i * k⁻¹) * k = i by group]
  exact hiX

theorem burnsideF42g_eq_top_of_fix1 {X : Subgroup G} {a b : G} (hbX : b ∈ X) (ha : a * a = 1)
    (hb : b * b = 1) (hfa : burnsideF42g_Fix1 X a) (hfb : burnsideF42g_Fix1 X b)
    (hab : ∀ x ∈ X, x * a * x⁻¹ ≠ b)
    (hinv : ∀ w : G, w * w = 1 → w ≠ 1 →
      ∃ k i : G, i ∈ X ∧ burnsideF42g_Fix1 X i ∧ w = k * i * k⁻¹)
    (g : G) : g ∈ X := by
  set b' := g * b * g⁻¹ with hb'def
  have hb'2 : b' * b' = 1 := by
    rw [hb'def]
    calc g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hb]; group
  rcases burnsideF42g_order_cases (a * b') with ⟨k, hk⟩ | ⟨m, hm, hm2⟩
  ·
    exfalso
    have hconj : (a * b') ^ k * a * ((a * b') ^ k)⁻¹ = b' := burnsideF42g_dihedral_odd ha hb'2 hk
    have hx : g⁻¹ * (a * b') ^ k * a * (g⁻¹ * (a * b') ^ k)⁻¹ = b := by
      calc g⁻¹ * (a * b') ^ k * a * (g⁻¹ * (a * b') ^ k)⁻¹
          = g⁻¹ * ((a * b') ^ k * a * ((a * b') ^ k)⁻¹) * g := by group
        _ = b := by rw [hconj, hb'def]; group
    have hkX : (g⁻¹ * (a * b') ^ k)⁻¹ ∈ X := by
      apply hfa
      rw [inv_inv, hx]
      exact hbX
    exact hab _ (by simpa using X.inv_mem hkX) hx
  ·
    obtain ⟨hw2, hw1, haw, hbw⟩ := burnsideF42g_dihedral_even ha hb'2 hm2 hm
    obtain ⟨k, i, hiX, hfi, hwk⟩ := hinv _ hw2 hw1
    have hk : k ∈ X := hfa k (burnsideF42g_fix_of_comm hiX hfi hwk haw)
    have hk' : g⁻¹ * k ∈ X := by
      apply hfb
      have := burnsideF42g_fix_of_comm hiX hfi hwk hbw
      rw [hb'def] at this
      rw [show (g⁻¹ * k)⁻¹ * b * (g⁻¹ * k) = k⁻¹ * (g * b * g⁻¹) * k by group]
      exact this
    have := X.mul_mem hk' (X.inv_mem hk)
    rw [mul_inv_cancel_right] at this
    simpa using X.inv_mem this

end LemmaB

section LemmaU

variable {G : Type*} [Group G] [Finite G]

theorem burnsideF42g_conj_va_mem {X : Subgroup G} {a v : G} (haX : a ∈ X)
    (hcen : ∀ x ∈ X, x * a = a * x) (ha : a * a = 1) (hfa : burnsideF42g_Fix1 X a)
    (hvX : v ∈ X) (hv : v * v = 1) (hfv : burnsideF42g_Fix1 X v) (hva : v ≠ a) (g : G) :
    g * (v * a) * g⁻¹ ∈ X := by
  have hconjX : ∀ x ∈ X, x * a * x⁻¹ = a := fun x hx => by
    rw [hcen x hx, mul_inv_cancel_right]
  set b := g * v * g⁻¹ with hbdef
  have hb2 : b * b = 1 := by
    rw [hbdef]
    calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [hv]; group
  rcases burnsideF42g_order_cases (a * b) with ⟨k, hk⟩ | ⟨m, hm, hm2⟩
  ·
    exfalso
    have hconj : (a * b) ^ k * a * ((a * b) ^ k)⁻¹ = b := burnsideF42g_dihedral_odd ha hb2 hk
    have hx : g⁻¹ * (a * b) ^ k * a * (g⁻¹ * (a * b) ^ k)⁻¹ = v := by
      calc g⁻¹ * (a * b) ^ k * a * (g⁻¹ * (a * b) ^ k)⁻¹
          = g⁻¹ * ((a * b) ^ k * a * ((a * b) ^ k)⁻¹) * g := by group
        _ = v := by rw [hconj, hbdef]; group
    have hxX : g⁻¹ * (a * b) ^ k ∈ X := by
      apply hfv
      rw [← hx, show (g⁻¹ * (a * b) ^ k)⁻¹ * (g⁻¹ * (a * b) ^ k * a * (g⁻¹ * (a * b) ^ k)⁻¹) *
        (g⁻¹ * (a * b) ^ k) = a by group]
      exact haX
    exact hva (by rw [← hx, hconjX _ hxX])
  · obtain ⟨hw2, hw1, haw, hbw⟩ := burnsideF42g_dihedral_even ha hb2 hm2 hm
    have hwX : (a * b) ^ m ∈ X := by
      apply hfa
      rw [mul_assoc, haw, ← mul_assoc, inv_mul_cancel, one_mul]
      exact haX
    obtain ⟨p, rfl | rfl⟩ := Nat.even_or_odd' m
    ·
      exfalso
      have hp : 0 < p := by omega
      have h4 := burnsideF42g_dihedral_four ha hb2 hm2 hp
      have hpX : ((a * b) ^ p)⁻¹ ∈ X := by
        apply hfa
        rw [inv_inv, h4]
        exact X.mul_mem haX hwX
      have hpX' : (a * b) ^ p ∈ X := by simpa using X.inv_mem hpX
      rw [hconjX _ hpX'] at h4
      exact hw1 (by
        have := congrArg (fun y => a⁻¹ * y) h4
        simpa using this.symm)
    ·
      have h2 := burnsideF42g_dihedral_two ha hb2 hm2
      have hyX : g⁻¹ * (b * (a * b) ^ (2 * p + 1)) * g ∈ X := by
        apply hfv
        have hcomm : (g⁻¹ * (b * (a * b) ^ (2 * p + 1)) * g) * v =
            v * (g⁻¹ * (b * (a * b) ^ (2 * p + 1)) * g) := by
          have hvb : v = g⁻¹ * b * g := by rw [hbdef]; group
          rw [hvb]
          calc g⁻¹ * (b * (a * b) ^ (2 * p + 1)) * g * (g⁻¹ * b * g)
              = g⁻¹ * (b * ((a * b) ^ (2 * p + 1) * b)) * g := by group
            _ = g⁻¹ * (b * (b * (a * b) ^ (2 * p + 1))) * g := by rw [hbw]
            _ = g⁻¹ * b * g * (g⁻¹ * (b * (a * b) ^ (2 * p + 1)) * g) := by group
        rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hvX
      rw [← h2] at hyX
      have hkX : ((a * b) ^ p)⁻¹ * g ∈ X := by
        apply hfa
        rw [show (((a * b) ^ p)⁻¹ * g)⁻¹ * a * (((a * b) ^ p)⁻¹ * g) =
          g⁻¹ * ((a * b) ^ p * a * ((a * b) ^ p)⁻¹) * g by group]
        exact hyX
      have hka : (((a * b) ^ p)⁻¹ * g)⁻¹ * a * (((a * b) ^ p)⁻¹ * g) = a := by
        have := hconjX _ (X.inv_mem hkX)
        simpa using this
      rw [show (((a * b) ^ p)⁻¹ * g)⁻¹ * a * (((a * b) ^ p)⁻¹ * g) =
        g⁻¹ * ((a * b) ^ p * a * ((a * b) ^ p)⁻¹) * g by group, h2] at hka
      have hw : (a * b) ^ (2 * p + 1) = g * (v * a) * g⁻¹ := by
        have e1 : b * (a * b) ^ (2 * p + 1) = g * a * g⁻¹ := by
          calc b * (a * b) ^ (2 * p + 1)
              = g * (g⁻¹ * (b * (a * b) ^ (2 * p + 1)) * g) * g⁻¹ := by group
            _ = g * a * g⁻¹ := by rw [hka]
        have hbi : b⁻¹ = b := burnsideF42g_inv_self hb2
        calc (a * b) ^ (2 * p + 1) = b⁻¹ * (b * (a * b) ^ (2 * p + 1)) := by group
          _ = b * (g * a * g⁻¹) := by rw [e1, hbi]
          _ = g * (v * a) * g⁻¹ := by rw [hbdef]; group
      rw [← hw]
      exact hwX

theorem burnsideF42g_eq_top_of_fix1_central {X : Subgroup G} {a v₁ v₂ : G} (haX : a ∈ X)
    (hcen : ∀ x ∈ X, x * a = a * x) (ha : a * a = 1) (hfa : burnsideF42g_Fix1 X a)
    (hv₁X : v₁ ∈ X) (hv₁ : v₁ * v₁ = 1) (hf₁ : burnsideF42g_Fix1 X v₁) (h₁ : v₁ ≠ a)
    (hv₂X : v₂ ∈ X) (hv₂ : v₂ * v₂ = 1) (hf₂ : burnsideF42g_Fix1 X v₂) (h₂ : v₂ ≠ a)
    (hf₁₂ : burnsideF42g_Fix1 X (v₁ * v₂)) (g : G) : g ∈ X := by
  have e1 := burnsideF42g_conj_va_mem haX hcen ha hfa hv₁X hv₁ hf₁ h₁ g
  have e2 := burnsideF42g_conj_va_mem haX hcen ha hfa hv₂X hv₂ hf₂ h₂ g
  have hav : a * v₂ = v₂ * a := (hcen v₂ hv₂X).symm
  have e : g * (v₁ * a) * g⁻¹ * (g * (v₂ * a) * g⁻¹) = (g⁻¹)⁻¹ * (v₁ * v₂) * g⁻¹ := by
    calc g * (v₁ * a) * g⁻¹ * (g * (v₂ * a) * g⁻¹) = g * (v₁ * (a * v₂) * a) * g⁻¹ := by group
      _ = g * (v₁ * v₂ * (a * a)) * g⁻¹ := by rw [hav]; group
      _ = (g⁻¹)⁻¹ * (v₁ * v₂) * g⁻¹ := by rw [ha]; group
  have := hf₁₂ g⁻¹ (e ▸ X.mul_mem e1 e2)
  simpa using X.inv_mem this

end LemmaU

end CFSG.ASVolI
