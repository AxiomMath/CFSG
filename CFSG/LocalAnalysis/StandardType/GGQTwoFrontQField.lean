module

public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType.QTwo

open CFSG.LieType.BorelTits

theorem qTwoFrontQ_exists_fixed {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    ∃ ω : K, unitaryInvolution K 2 f ω = ω ∧ ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq] at hcard
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨x, hx0, hx1⟩ : ∃ x : K, x ≠ 0 ∧ x ^ (q + 1) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ.erase (0 : K)) ⊆ (Polynomial.nthRoots (q + 1) (1 : K)).toFinset := by
      intro x hx
      have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.succ_pos q)]
      exact hcon x hx0
    have h1 := Finset.card_le_card hsub
    have h2 : (Polynomial.nthRoots (q + 1) (1 : K)).toFinset.card ≤ q + 1 :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard] at h1
    have hpos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h3 : q ^ 2 ≤ q + 2 := by omega
    nlinarith [hq4]
  refine ⟨x ^ (q + 1), ?_, pow_ne_zero _ hx0, hx1⟩
  have hx : x ^ (q ^ 2 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one x hx0
    rwa [hcard] at this
  have hpos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [unitaryInvolution_apply, ← hq, ← pow_mul]
  calc x ^ ((q + 1) * q) = x ^ (q + 1) * x ^ (q ^ 2 - 1) := by
        rw [← pow_add]
        congr 1
        zify [hpos]
        ring
    _ = x ^ (q + 1) := by rw [hx, mul_one]

end CFSG.StandardType.QTwo

end
