module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2FldGcd
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

variable {k : Type} [Field k]

theorem eq_of_pow_two_pow_eq' [CharP k 2] {x y : k} {r : ℕ} (h : x ^ 2 ^ r = y ^ 2 ^ r) :
    x = y := by
  have h1 : (x - y) ^ 2 ^ r = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero r two_ne_zero) |>.mp h1)

theorem twist_const {c₀ b₀ A B : k} (hc₀ : c₀ ≠ 0) (hb₀ : b₀ ≠ 0) (hA : A ≠ 0) (s r : ℕ) :
    ∃ D M : k, D ≠ 0 ∧ ∀ y y' : k, y ≠ 0 → c₀ * y' = A * (b₀ * y ^ 2 ^ s) ^ 2 ^ (r + 1) →
      b₀ * y' ^ 2 ^ s = B * (c₀ * y) ^ 2 ^ r →
      D * (y ^ (2 ^ (2 * s + 1) - 1)) ^ 2 ^ r = M := by
  set L : k := c₀⁻¹ * A * b₀ ^ 2 ^ (r + 1) with hL
  refine ⟨b₀ * L ^ 2 ^ s, B * c₀ ^ 2 ^ r, ?_, ?_⟩
  · exact mul_ne_zero hb₀ (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (inv_ne_zero hc₀) hA)
      (pow_ne_zero _ hb₀)))
  · intro y y' hy E1 E2
    have hy' : y' = L * y ^ (2 ^ s * 2 ^ (r + 1)) := by
      have h1 : y' = c₀⁻¹ * (c₀ * y') := by field_simp
      rw [h1, E1, mul_pow, ← pow_mul, hL]
      ring
    have hexp : 2 ^ s * 2 ^ (r + 1) * 2 ^ s = 2 ^ (2 * s + 1) * 2 ^ r := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      ring
    have hE2 : b₀ * L ^ 2 ^ s * y ^ (2 ^ (2 * s + 1) * 2 ^ r) = B * c₀ ^ 2 ^ r * y ^ 2 ^ r := by
      rw [← hexp]
      have h2 := E2
      rw [hy', mul_pow, ← pow_mul, mul_pow] at h2
      linear_combination h2
    have he : y ^ (2 ^ (2 * s + 1)) = y ^ (2 ^ (2 * s + 1) - 1) * y := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
    rw [pow_mul, he, mul_pow] at hE2
    have hyr : y ^ 2 ^ r ≠ 0 := pow_ne_zero _ hy
    apply mul_right_cancel₀ hyr
    linear_combination hE2

theorem pow_two_pow_add_mul {f : k} {g : ℕ} (h : f ^ 2 ^ g = f) (a j : ℕ) :
    f ^ 2 ^ (a + g * j) = f ^ 2 ^ a := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc f ^ 2 ^ (a + g * (j + 1)) = f ^ (2 ^ g * 2 ^ (a + g * j)) := by
          rw [← pow_add]
          congr 2
          ring
      _ = (f ^ 2 ^ g) ^ 2 ^ (a + g * j) := pow_mul _ _ _
      _ = f ^ 2 ^ (a + g * j) := by rw [h]
      _ = f ^ 2 ^ a := ih

variable [Finite k]

theorem four_le_card {F : Subfield k} {a b c d : k} (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F)
    (hd : d ∈ F) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : 4 ≤ Nat.card F := by
  classical
  have := Fintype.ofFinite k
  have h : ({a, b, c, d} : Finset k) ⊆ Finset.univ.filter (· ∈ F) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, d} : Finset k).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hcd]
    · simpa using ⟨hbc, hbd⟩
    · simpa using ⟨hab, hac, had⟩
  calc 4 = ({a, b, c, d} : Finset k).card := hcard.symm
    _ ≤ (Finset.univ.filter (· ∈ F)).card := Finset.card_le_card h
    _ = Nat.card F := by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem pow_natCard_of_mem {F : Subfield k} {f : k} (hf : f ∈ F) : f ^ Nat.card F = f := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card (⟨f, hf⟩ : F)
  rw [Fintype.card_eq_nat_card] at h
  exact congrArg Subtype.val h

theorem twist_shape [CharP k 2] {n : ℕ} (hn : Nat.card k = 2 ^ n) {c₀ b₀ A B : k}
    (hc₀ : c₀ ≠ 0) (hb₀ : b₀ ≠ 0) (hA : A ≠ 0) {s r : ℕ} {Y : Set k}
    (htw : ∀ y ∈ Y, ∃ y' ∈ Y, c₀ * y' = A * (b₀ * y ^ 2 ^ s) ^ 2 ^ (r + 1) ∧
      b₀ * y' ^ 2 ^ s = B * (c₀ * y) ^ 2 ^ r)
    {y₀ y₂ y₃ : k} (h₀ : y₀ ∈ Y) (h₂ : y₂ ∈ Y) (h₃ : y₃ ∈ Y) (n₀ : y₀ ≠ 0) (n₂ : y₂ ≠ 0)
    (n₃ : y₃ ≠ 0) (d₀₂ : y₀ ≠ y₂) (d₀₃ : y₀ ≠ y₃) (d₂₃ : y₂ ≠ y₃) :
    ∃ (a : ℕ) (F₀ : Subfield k), 1 ≤ a ∧ Nat.card F₀ = 2 ^ (2 * a + 1) ∧
      (∀ f ∈ F₀, f ^ 2 ^ (2 * a + 1) = f) ∧ (∀ f ∈ F₀, f ^ 2 ^ s = f ^ 2 ^ a) ∧
      ∀ y ∈ Y, ∃ f ∈ F₀, y = y₀ * f := by
  obtain ⟨D, M, hD, hDM⟩ := twist_const hc₀ hb₀ hA s r
  obtain ⟨F₀, hcard, hmem⟩ := exists_subfield_of_gcd hn s
  have hconst : ∀ y ∈ Y, y ≠ 0 → y ^ (2 ^ (2 * s + 1) - 1) = y₀ ^ (2 ^ (2 * s + 1) - 1) := by
    intro y hy hy0
    obtain ⟨y', -, E1, E2⟩ := htw y hy
    obtain ⟨y₀', -, E1₀, E2₀⟩ := htw y₀ h₀
    have h3 : (y ^ (2 ^ (2 * s + 1) - 1)) ^ 2 ^ r = (y₀ ^ (2 ^ (2 * s + 1) - 1)) ^ 2 ^ r :=
      mul_left_cancel₀ hD ((hDM y y' hy0 E1 E2).trans (hDM y₀ y₀' n₀ E1₀ E2₀).symm)
    exact eq_of_pow_two_pow_eq' h3
  have hY : ∀ y ∈ Y, ∃ f ∈ F₀, y = y₀ * f := by
    intro y hy
    by_cases hy0 : y = 0
    · exact ⟨0, F₀.zero_mem, by simp [hy0]⟩
    · refine ⟨y / y₀, (hmem _ (div_ne_zero hy0 n₀)).1 ?_, by field_simp⟩
      rw [div_pow, hconst y hy hy0, div_self (pow_ne_zero _ n₀)]
  have hmem' : ∀ y ∈ Y, y ≠ 0 → y / y₀ ∈ F₀ := by
    intro y hy hy0
    obtain ⟨f, hf, rfl⟩ := hY y hy
    have : y₀ * f / y₀ = f := by field_simp
    rw [this]
    exact hf
  have h4 : 4 ≤ Nat.card F₀ :=
    four_le_card F₀.zero_mem F₀.one_mem (hmem' y₂ h₂ n₂) (hmem' y₃ h₃ n₃) zero_ne_one
      (fun h => n₂ (div_eq_zero_iff.1 h.symm |>.resolve_right n₀))
      (fun h => n₃ (div_eq_zero_iff.1 h.symm |>.resolve_right n₀))
      (fun h => d₀₂ (by field_simp at h; exact h))
      (fun h => d₀₃ (by field_simp at h; exact h))
      (fun h => d₂₃ (by field_simp at h; exact h))
  set g := Nat.gcd (2 * s + 1) n with hg
  rw [hcard] at h4
  have hg2 : 2 ≤ g := by
    by_contra hlt
    push Not at hlt
    interval_cases g <;> simp at h4
  have hodd : Odd g := Odd.of_dvd_nat (odd_two_mul_add_one s) (Nat.gcd_dvd_left _ _)
  obtain ⟨a, ha⟩ := hodd
  have ha1 : 1 ≤ a := by omega
  rw [ha] at hcard
  have hferm : ∀ f ∈ F₀, f ^ 2 ^ (2 * a + 1) = f := by
    intro f hf
    have := pow_natCard_of_mem hf
    rwa [hcard] at this
  obtain ⟨j, hj⟩ := Nat.gcd_dvd_left (2 * s + 1) n
  rw [← hg, ha] at hj
  have hjodd : Odd j := (Nat.odd_mul.1 (hj ▸ odd_two_mul_add_one s : Odd ((2 * a + 1) * j))).2
  obtain ⟨j', hj'⟩ := hjodd
  have hs : s = a + (2 * a + 1) * j' := by
    subst hj'
    nlinarith [hj]
  refine ⟨a, F₀, ha1, hcard, hferm, fun f hf => ?_, hY⟩
  rw [hs]
  exact pow_two_pow_add_mul (hferm f hf) a j'

end CFSG.Quasithin.Ch3E213M.Sp4C2
