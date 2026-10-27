module

public import CFSG.Quasithin.SteinbergCDSimpleSylowProduct
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.SteinbergBQ

open CFSG.Assembly.ComponentType (ClassicalModel)
open CFSG.ComponentClassification.ClassicalModelStatedBridge
open scoped Pointwise

theorem card_of_classicalModel_psl {S : Type} [Group S] {n p f : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    (hS : ClassicalModel S .PSL n p f) :
    Nat.card S = (p ^ f) ^ (n * (n - 1) / 2) * (∏ j ∈ Finset.Icc 2 n, ((p ^ f) ^ j - 1)) /
      Nat.gcd n (p ^ f - 1) := by
  obtain ⟨⟨-, hf, -, -⟩, ⟨e⟩⟩ := hS
  rw [Nat.card_congr (e.trans (pslModelEquiv n p f)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL hn, GaloisField.card p f (by omega)]

theorem small_classical_model_three_free_sylow_product_rigidity {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (_hnab : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ} [Fact p.Prime]
    (hnpf : (n, p, f) = (2, 2, 2) ∨ (n, p, f) = (2, 5, 1) ∨ (n, p, f) = (2, 7, 1) ∨
      (n, p, f) = (3, 2, 1))
    (hS : ClassicalModel S .PSL n p f) (T : Sylow 2 S) (A : Subgroup S)
    (hA : ¬ 3 ∣ Nat.card A) (hAT : (A : Set S) * (T : Set S) = (T : Set S) * (A : Set S)) :
    A ≤ T := by
  have hcard : Nat.card S = 2 ^ 2 * 3 * 5 ∨ Nat.card S = 2 ^ 3 * 3 * 7 := by
    rcases hnpf with h | h | h | h <;>
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [card_of_classicalModel_psl (by norm_num) hS]
      decide
  rcases hcard with h | h
  · exact CFSG.Quasithin.SteinbergCD.simple_order_two_power_three_prime_sylow_product_rigidity
      (by norm_num) (by norm_num) h T A hA hAT
  · exact CFSG.Quasithin.SteinbergCD.simple_order_two_power_three_prime_sylow_product_rigidity
      (by norm_num) (by norm_num) h T A hA hAT

end CFSG.Quasithin.SteinbergBQ
