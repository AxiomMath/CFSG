module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseJNCoset
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseIndexCoset
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise BigOperators

namespace CFSG.GorensteinWalter

universe u

private lemma sum_range_eq_first_five
    (f : ℕ → ℕ) (hvanish : ∀ n : ℕ, 5 ≤ n → f n = 0) :
    ∀ K : ℕ, 5 ≤ K →
      (∑ n ∈ Finset.range K, f n) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  intro K
  induction K with
  | zero => intro h; omega
  | succ K ih =>
      intro hK
      by_cases hlt : K < 5
      · have hK4 : K = 4 := by omega
        subst K
        simp [Finset.sum_range_succ]
      · have hK5 : 5 ≤ K := by omega
        rw [Finset.sum_range_succ, ih hK5, hvanish K hK5]
        omega

/-!
Finite support reduction for the source's (b_n)-bookkeeping.  Once all
fibres of size at least five vanish, the generic coset partition identities
reduce to the five displayed values (b_0,ldots,b_4).
-/

public theorem firstCase_count_support_five
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hvanish : ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0)
    (hJge : 4 ≤ Nat.card {x : G // IsInvolution x}) :
    ∃ b0 b1 b2 b3 b4 : ℕ,
      (∀ n : ℕ, n ≤ 4 →
        Nat.card {x : G // x ∈ firstCaseJ c n} =
          n * firstCaseBn b0 b1 b2 b3 b4 n) ∧
      c.Hhat.index = 1 + b0 + b1 + b2 + b3 + b4 ∧
      Nat.card {x : G // IsInvolution x} =
        Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} +
          (b1 + 2 * b2 + 3 * b3 + 4 * b4) := by
  let b0 := cosetInvolution_b c.Hhat 0
  let b1 := cosetInvolution_b c.Hhat 1
  let b2 := cosetInvolution_b c.Hhat 2
  let b3 := cosetInvolution_b c.Hhat 3
  let b4 := cosetInvolution_b c.Hhat 4
  refine ⟨b0, b1, b2, b3, b4, ?_, ?_, ?_⟩
  · intro n hn
    have hJn := firstCase_J_n_card c n
    interval_cases n <;>
      simpa [b0, b1, b2, b3, b4, firstCaseBn] using hJn
  · have hidx := firstCase_index_eq_one_add_sum_coset_b c
    have hJ : 5 ≤ Nat.card {x : G // IsInvolution x} + 1 := by omega
    have hsum := sum_range_eq_first_five
      (fun n => cosetInvolution_b c.Hhat n) hvanish _ hJ
    rw [hsum] at hidx
    simpa [b0, b1, b2, b3, b4, Nat.add_assoc] using hidx
  · have htot := cosetInvolution_J_card_eq_base_add_sum c.Hhat
    have hJ : 5 ≤ Nat.card {x : G // IsInvolution x} + 1 := by omega
    have hsum := sum_range_eq_first_five
      (fun n => n * cosetInvolution_b c.Hhat n)
      (fun n hn => by rw [hvanish n hn, mul_zero]) _ hJ
    rw [hsum] at htot
    simpa [b0, b1, b2, b3, b4, Nat.zero_mul, firstCaseBn] using htot

end CFSG.GorensteinWalter
