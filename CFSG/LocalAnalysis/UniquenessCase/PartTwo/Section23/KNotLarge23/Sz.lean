module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Orders
import CFSG.Blueprint.LieModelAPI
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem not_three_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize q ^ 2 = q2 at hq2 ⊢
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h <;> omega
  · omega

theorem knl_sz {Q : Type} [Group Q] [Finite Q] {a : ℕ}
    (hQ : IsSz Q a) (N : Subgroup Q) [N.Normal] {n : ℕ} (hn : 3 ≤ n) :
    ¬ (IsSLn (Q ⧸ N) 3 n ∨ IsSp4 (Q ⧸ N) n ∨ IsU4 (Q ⧸ N) n) := by
  intro hT
  have hord := card_target (by omega) hT
  have h3 : 3 ∣ Nat.card (Q ⧸ N) := knl_three_dvd_order hord
  obtain ⟨-, -, a', -, K, hF, hFin, hf, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.twistedB2_iff.1 hQ
  let _inst : Field K := hF
  have := hFin
  have hK' : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hK, hf]
  have hcard : Nat.card Q = (2 ^ (2 * a' + 1)) ^ 2 * (2 ^ (2 * a' + 1) - 1) *
      ((2 ^ (2 * a' + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK']
  have hdvd : 3 ∣ Nat.card Q := by
    refine h3.trans ?_
    rw [card_quotient_eq_index]
    exact Subgroup.index_dvd_card N
  rw [hcard] at hdvd
  exact not_three_dvd_suzuki_order a' hdvd

end CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23

end
