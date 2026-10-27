module

public import CFSG.Fischer.Classification.SRG.Conference
import CFSG.OddTranspositions.PartFour.PowerTwoDiff

public section

namespace CFSG.OddTranspositions.PartFour

private lemma two_pow_add_two_pow_eq_two_pow {p q r : ℕ} (hpq : p ≤ q)
    (h : 2 ^ p + 2 ^ q = 2 ^ r) : p = q ∧ r = q + 1 := by
  have hqle : 2 ^ q ≤ 2 ^ r := h ▸ Nat.le_add_left _ _
  have hqr : q ≤ r := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hqle
  have hle : 2 ^ r ≤ 2 ^ (q + 1) := by
    rw [← h, Nat.two_pow_succ]
    exact Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) hpq) _
  have hrq1 : r ≤ q + 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have hq : r = q + 1 := by
    rcases Nat.lt_or_ge r (q + 1) with hlt | hge
    · have hrq' : r = q := Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hqr
      simp [hrq'] at h
    · exact Nat.le_antisymm hrq1 hge
  have hpq' : 2 ^ p = 2 ^ q := by
    have h2 : 2 ^ p + 2 ^ q = 2 ^ q + 2 ^ q := by
      rw [h, hq, Nat.two_pow_succ]
    exact Nat.add_right_cancel h2
  exact ⟨(Nat.pow_right_injective (by norm_num : 2 ≤ 2)) hpq', hq⟩

private lemma discr_cast (a s : ℕ) :
    (((2 ^ s) ^ 2 + 2 ^ (a + s + 2) : ℕ) : ℤ) =
      (((2 ^ s - 1 : ℕ) : ℤ) - 1) ^ 2 +
        4 * ((((2 ^ a + 1) * 2 ^ s : ℕ) : ℤ) - 1) := by
  have h1 : ((2 ^ s - 1 : ℕ) : ℤ) = (2 : ℤ) ^ s - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow)]
    push_cast
    norm_num
  have h2 : (((2 ^ a + 1) * 2 ^ s : ℕ) : ℤ) = ((2 : ℤ) ^ a + 1) * (2 : ℤ) ^ s := by
    push_cast
    ring
  have h3 : (((2 ^ s) ^ 2 + 2 ^ (a + s + 2) : ℕ) : ℤ) =
      ((2 : ℤ) ^ s) ^ 2 + (2 : ℤ) ^ (a + s + 2) := by
    push_cast
    ring
  rw [h1, h2, h3]
  rw [show a + s + 2 = (a + s) + 2 by ring, pow_add, pow_add]
  ring

theorem eq_add_one_of_isSRGWith_two_pow {V : Type*} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] {n a s : ℕ} (h : Γ.IsSRGWith n ((2 ^ a + 1) * 2 ^ s) (2 ^ s - 1) 1)
    (hn : 0 < n) (hs : 1 ≤ s) : a = s + 1 := by
  have hD := discr_cast a s
  by_cases hsq : IsSquare ((((2 ^ s - 1 : ℕ) : ℤ) - 1) ^ 2 +
      4 * ((((2 ^ a + 1) * 2 ^ s : ℕ) : ℤ) - 1))
  · obtain ⟨r, hr⟩ := hsq
    have hnat : r.natAbs ^ 2 = (2 ^ s) ^ 2 + 2 ^ (a + s + 2) := by
      have h' : (((2 ^ s) ^ 2 + 2 ^ (a + s + 2) : ℕ) : ℤ) = r * r := by
        rw [hD]
        exact hr
      have h'' := congrArg Int.natAbs h'
      rw [Int.natAbs_natCast, Int.natAbs_mul] at h''
      rw [pow_two]
      exact h''.symm
    obtain ⟨b, c, -, hbca, -, h2y⟩ :=
      lemma16_3_one (x := r.natAbs) (y := 2 ^ s) (a := a + s + 2) hnat.symm
    have h2y' : 2 ^ b + 2 ^ (s + 1) = 2 ^ c := by
      rw [pow_succ]
      omega
    have hbcases : b = s + 1 ∧ c = s + 2 := by
      rcases le_total b (s + 1) with hble | hble
      · obtain ⟨hb, hc⟩ := two_pow_add_two_pow_eq_two_pow hble h2y'
        exact ⟨hb, by omega⟩
      · obtain ⟨hb, hc⟩ :=
          two_pow_add_two_pow_eq_two_pow hble (by rw [add_comm]; exact h2y')
        exact ⟨hb.symm, by omega⟩
    obtain ⟨hb, hc⟩ := hbcases
    omega
  · obtain ⟨-, h2⟩ := h.conference_of_not_isSquare hn hsq
    have hkpos : (0 : ℤ) < (((2 ^ a + 1) * 2 ^ s : ℕ) : ℤ) := by
      have : 0 < (2 ^ a + 1) * 2 ^ s := by positivity
      exact_mod_cast this
    have hℓ : (0 : ℤ) ≤ ((2 ^ s - 1 : ℕ) : ℤ) - 1 := by
      have h2s : 2 ≤ 2 ^ s := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
      have : (2 : ℤ) ≤ ((2 ^ s : ℕ) : ℤ) := by exact_mod_cast h2s
      rw [Nat.cast_sub (Nat.one_le_two_pow)]
      push_cast
      linarith
    have hn1 : (0 : ℤ) ≤ (n : ℤ) - 1 := by
      have : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      linarith
    have h2' : 2 * (((2 ^ a + 1) * 2 ^ s : ℕ) : ℤ) +
        ((n : ℤ) - 1) * (((2 ^ s - 1 : ℕ) : ℤ) - 1) = 0 := h2
    have hprod : (0 : ℤ) ≤
        ((n : ℤ) - 1) * (((2 ^ s - 1 : ℕ) : ℤ) - 1) :=
      mul_nonneg hn1 hℓ
    have hk2 : (0 : ℤ) < 2 * (((2 ^ a + 1) * 2 ^ s : ℕ) : ℤ) := by linarith
    linarith

end CFSG.OddTranspositions.PartFour
