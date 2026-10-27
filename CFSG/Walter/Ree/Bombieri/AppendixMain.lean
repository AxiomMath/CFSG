module

public import CFSG.Walter.Ree.Bombieri.AppData
public import CFSG.Walter.Ree.Defs
import CFSG.Walter.Ree.Bombieri.Appendix
import CFSG.Walter.Ree.Bombieri.Galois
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Walter.Ree.Bombieri

variable {K : Type*} [Field K] [Fintype K] [CharP K 3]

theorem sq_eq_frob_of_checkK {k : ℕ} (hk : 2 ≤ k) (hK : Fintype.card K = 3 ^ k) {f : F3P}
    (hc : F3P.checkK f k = true) {σ : K ≃+* K} (hσ : IsThompsonAut K σ) :
    ∀ x, σ (σ x) = x ^ 3 := by
  obtain ⟨hA, a, s, ha, -, hB1, hB2, hC⟩ := hσ
  obtain ⟨b, hbk, hb⟩ := exists_eq_frob_pow hK σ
  simp only [F3P.checkK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨hroot, hall⟩ := hc
  have hcop : Nat.Coprime b k := coprime_of_generates hK hk hb hA
  by_cases h2b : 2 * b % k = 1
  · intro x
    rw [hb, hb, ← pow_mul, ← pow_add, ← two_mul, pow_three_pow_mod hK, h2b, pow_one]
  · have hgcd : Nat.Coprime (3 ^ b + 2) (3 ^ k - 1) :=
      coprime_of_bijective_pow hK (s := s) fun x => by
        have := hB2 x; rwa [hb, ← pow_add] at this
    have hcase : F3P.checkCase f k b = true := by
      have := hall b hbk
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
      rcases this with ((h | h) | h) | h
      · exact absurd hcop h
      · exact absurd h h2b
      · exact absurd hgcd h
      · exact h
    have hfv : f.Valid := by
      simp only [F3P.rootCheck, Bool.and_eq_true, beq_iff_eq] at hroot
      exact (F3P.valid_iff f).mpr hroot.1.1.1
    obtain ⟨r, hr⟩ := exists_root_of_rootCheck hK hroot
    obtain ⟨p, hp, hT⟩ := checkCase_sound hK hfv hr hcase hb ha hB1
    exact absurd (hC p hp) hT

theorem sq_eq_frob_of_checkRange {lo hi : ℕ} (hc : checkRange lo hi = true) {k : ℕ}
    (hk : 3 ≤ k) (hodd : k % 2 = 1) (hlo : lo ≤ k) (hhi : k ≤ hi)
    (hK : Fintype.card K = 3 ^ k) {σ : K ≃+* K} (hσ : IsThompsonAut K σ) :
    ∀ x, σ (σ x) = x ^ 3 := by
  simp only [checkRange, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hc
  have := hc (k - lo) (by omega)
  rw [show lo + (k - lo) = k by omega] at this
  rcases this with h | h
  · omega
  · exact sq_eq_frob_of_checkK (by omega) hK h hσ

end CFSG.Walter.Ree.Bombieri
