module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.Wreath

variable {C S : Type} [CommGroup C] [Group S]

@[expose] def sh (x : Fin 3 → C) : Fin 3 → C := fun i => x (i - 1)

theorem sh_mul (x y : Fin 3 → C) : sh (x * y) = sh x * sh y := rfl

theorem conj_pow_mem {B : Subgroup S} {s : S} (hn : ∀ b ∈ B, s * b * s⁻¹ ∈ B) (k : ℕ) :
    ∀ c ∈ B, s ^ k * c * (s ^ k)⁻¹ ∈ B := by
  induction k with
  | zero => intro c hc; simpa using hc
  | succ k ih =>
    intro c hc
    have e : s ^ (k + 1) * c * (s ^ (k + 1))⁻¹ = s * (s ^ k * c * (s ^ k)⁻¹) * s⁻¹ := by group
    rw [e]
    exact hn _ (ih c hc)

theorem inv_pow_eq {s : S} (hs3 : s ^ 3 = 1) (k : ℕ) : (s ^ k)⁻¹ = s ^ (2 * k) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hs3, one_pow]

@[expose] def extSub (B : Subgroup S) (s : S) (hs3 : s ^ 3 = 1)
    (hn : ∀ b ∈ B, s * b * s⁻¹ ∈ B) : Subgroup S where
  carrier := {u | ∃ b ∈ B, ∃ k : ℕ, k < 3 ∧ u = b * s ^ k}
  one_mem' := ⟨1, B.one_mem, 0, by norm_num, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨b, hb, i, hi, rfl⟩ ⟨b', hb', j, hj, rfl⟩
    refine ⟨b * (s ^ i * b' * (s ^ i)⁻¹), B.mul_mem hb (conj_pow_mem hn i b' hb'),
      (i + j) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← pow_eq_pow_mod _ hs3, pow_add]
    group
  inv_mem' := by
    rintro _ ⟨b, hb, k, hk, rfl⟩
    refine ⟨s ^ (2 * k) * b⁻¹ * (s ^ (2 * k))⁻¹, conj_pow_mem hn _ _ (B.inv_mem hb),
      (2 * k) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← pow_eq_pow_mod _ hs3, mul_inv_rev, inv_pow_eq hs3, ← inv_pow_eq hs3]
    group

theorem three_dvd_of_pow_mem {B : Subgroup S} {s : S} (hs3 : s ^ 3 = 1) (hsB : s ∉ B) {k : ℕ}
    (hk : s ^ k ∈ B) : 3 ∣ k := by
  rw [pow_eq_pow_mod k hs3] at hk
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
  · exact Nat.dvd_of_mod_eq_zero h0
  · rw [h1, pow_one] at hk
    exact absurd hk hsB
  · rw [h2] at hk
    have e : (s ^ 2) ^ 2 = s := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hs3, one_mul]
    exact absurd (e ▸ B.pow_mem hk 2) hsB

theorem card_extSub (B : Subgroup S) (s : S) (hs3 : s ^ 3 = 1) (hn : ∀ b ∈ B, s * b * s⁻¹ ∈ B)
    (hsB : s ∉ B) : Nat.card (extSub B s hs3 hn) = Nat.card B * 3 := by
  have hf : Function.Bijective (fun p : B × Fin 3 =>
      (⟨(p.1 : S) * s ^ (p.2 : ℕ), p.1, p.1.2, p.2, p.2.2, rfl⟩ : extSub B s hs3 hn)) := by
    constructor
    · rintro ⟨⟨b, hb⟩, i⟩ ⟨⟨b', hb'⟩, j⟩ h
      replace h : b * s ^ (i : ℕ) = b' * s ^ (j : ℕ) := congrArg Subtype.val h
      have hij : (i : ℕ) = j := by
        have e : s ^ ((i : ℕ) + 2 * j) = b⁻¹ * b' := by
          rw [pow_add, ← inv_pow_eq hs3]
          calc s ^ (i : ℕ) * (s ^ (j : ℕ))⁻¹
              = b⁻¹ * (b * s ^ (i : ℕ)) * (s ^ (j : ℕ))⁻¹ := by group
            _ = b⁻¹ * (b' * s ^ (j : ℕ)) * (s ^ (j : ℕ))⁻¹ := by rw [h]
            _ = b⁻¹ * b' := by group
        have h1 : s ^ ((i : ℕ) + 2 * j) ∈ B := by
          rw [e]
          exact B.mul_mem (B.inv_mem hb) hb'
        have := three_dvd_of_pow_mem hs3 hsB h1
        have hi := i.2
        have hj := j.2
        omega
      have hij' : i = j := Fin.ext hij
      subst hij'
      have : b = b' := mul_right_cancel h
      subst this
      rfl
    · rintro ⟨u, b, hb, k, hk, rfl⟩
      exact ⟨(⟨b, hb⟩, ⟨k, hk⟩), rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hf).symm, Nat.card_prod]
  simp

@[expose] def shHom : (Fin 3 → C) →* (Fin 3 → C) where
  toFun := sh
  map_one' := rfl
  map_mul' := sh_mul

theorem inv_sq_of_pow_three {z : C} (hz3 : z ^ 3 = 1) : (z ^ 2)⁻¹ = z :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hz3)

theorem wreath_w1 {z : C} (hz3 : z ^ 3 = 1) :
    (fun i : Fin 3 => z ^ (i : ℕ)) * (shHom (fun i : Fin 3 => z ^ (i : ℕ)))⁻¹ = fun _ => z := by
  funext i
  fin_cases i
  · show z ^ 0 * (z ^ 2)⁻¹ = z
    rw [pow_zero, one_mul, inv_sq_of_pow_three hz3]
  · show z ^ 1 * (z ^ 0)⁻¹ = z
    rw [pow_zero, inv_one, mul_one, pow_one]
  · show z ^ 2 * (z ^ 1)⁻¹ = z
    rw [pow_one]
    group

theorem wreath_w2 {z : C} (hz3 : z ^ 3 = 1) :
    (fun i : Fin 3 => (z ^ (i : ℕ))⁻¹) *
      ((shHom.comp shHom) (fun i : Fin 3 => (z ^ (i : ℕ))⁻¹))⁻¹ = fun _ => z := by
  funext i
  fin_cases i
  · show (z ^ 0)⁻¹ * ((z ^ 1)⁻¹)⁻¹ = z
    rw [pow_zero, inv_one, one_mul, pow_one, inv_inv]
  · show (z ^ 1)⁻¹ * ((z ^ 2)⁻¹)⁻¹ = z
    rw [pow_one]
    group
  · show (z ^ 2)⁻¹ * ((z ^ 0)⁻¹)⁻¹ = z
    rw [pow_zero, inv_one, inv_one, mul_one, inv_sq_of_pow_three hz3]

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.Wreath
