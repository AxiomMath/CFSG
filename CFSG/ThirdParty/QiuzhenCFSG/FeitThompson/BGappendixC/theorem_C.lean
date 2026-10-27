module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGappendixC.lemma_C_3

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

noncomputable section

universe u v

variable (p q : ℕ) [Fact p.Prime]

/-- Theorem C. Under conditions `(A)` and `(B)`, `p ≤ q`. -/
public theorem CFSG.appendixC_theorem_C
    [Fact q.Prime]
    (hA : appendixCConditionA p q)
    (hB : appendixCConditionB p q) :
    p ≤ q := by
  have hp : Nat.Prime p := Fact.out
  have hq : Nat.Prime q := Fact.out
  by_cases hp2 : p = 2
  · simpa [hp2] using hq.two_le
  by_cases hq2 : q = 2
  · have hoddp : Odd p := hp.odd_of_ne_two hp2
    have hquot : (p ^ q - 1) / (p - 1) = p + 1 := by
      rw [hq2]
      rw [show p ^ 2 - 1 = (p - 1) * (p + 1) by
        rw [Nat.mul_comm]
        simpa using (Nat.sq_sub_sq p 1)]
      exact Nat.mul_div_right (p + 1) (Nat.sub_pos_of_lt hp.one_lt)
    have h2dvd_plus : 2 ∣ p + 1 := by
      rcases hoddp with ⟨k, hk⟩
      use k + 1
      omega
    have h2dvd_minus : 2 ∣ p - 1 := by
      rcases hoddp with ⟨k, hk⟩
      use k
      omega
    have hnot : ¬ Nat.Coprime (p + 1) (p - 1) :=
      Nat.not_coprime_of_dvd_of_dvd (by norm_num) h2dvd_plus h2dvd_minus
    exact False.elim (hnot (by simpa [appendixCConditionA, hquot] using hA))
  by_cases hp3 : p = 3
  · subst p
    have hoddq : Odd q := hq.odd_of_ne_two hq2
    rcases hoddq with ⟨k, hk⟩
    have hq2le : 2 ≤ q := hq.two_le
    omega
  · have hoddp : Odd p := hp.odd_of_ne_two hp2
    have hoddq : Odd q := hq.odd_of_ne_two hq2
    exact appendixC_lemma_C_1 (p := p) (q := q)
      (appendixC_lemma_C_3_of_p_ne_three (p := p) (q := q)
        hA hoddp hoddq hp3 hB)
      (appendixC_lemma_C_2 (p := p) (q := q) hA hoddp hoddq)

end
