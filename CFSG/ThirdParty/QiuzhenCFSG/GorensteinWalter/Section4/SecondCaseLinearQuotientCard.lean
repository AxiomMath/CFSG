module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2QuotientTorusCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cardinality of the linear component quotient in complementary-half form
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private lemma two_mul_div_two_of_even {n : ℕ} (hn : Even n) :
    (n / 2) * 2 = n := by
  rcases hn with ⟨k, hk⟩
  omega

private lemma complementary_half_product {q a b : ℕ} (hq : Odd q)
    (ha : a = (q - 1) / 2 ∨ a = (q + 1) / 2)
    (hb : b = (q - 1) / 2 ∨ b = (q + 1) / 2)
    (haEven : Even a) (hbOdd : Odd b) :
    2 * a * (2 * b) = q ^ 2 - 1 := by
  rcases ha with ha1 | ha2
  · rcases hb with hb1 | hb2
    · exfalso
      have hEq : a = b := ha1.trans hb1.symm
      have hEven' : Even b := by simpa [hEq] using haEven
      rcases hbOdd with ⟨k, hk⟩
      rcases hEven' with ⟨l, hl⟩
      omega
    · have h2a : 2 * a = q - 1 := by
        rw [ha1, mul_comm]
        exact two_mul_div_two_of_even (by
          rcases hq with ⟨m, hm⟩
          use m
          omega)
      have h2b : 2 * b = q + 1 := by
        rw [hb2, mul_comm]
        exact two_mul_div_two_of_even (by
          rcases hq with ⟨m, hm⟩
          use m + 1
          omega)
      calc
        2 * a * (2 * b) = (q - 1) * (q + 1) := by rw [h2a, h2b]
        _ = q ^ 2 - 1 := by
          rcases hq with ⟨m, hm⟩
          rw [hm]
          have h : (2 * m + 1) ^ 2 = 2 * m * (2 * m + 2) + 1 := by ring
          calc
            (2 * m) * (2 * m + 2) = (2 * m * (2 * m + 2) + 1) - 1 := by omega
            _ = (2 * m + 1) ^ 2 - 1 := by rw [h]
  · rcases hb with hb1 | hb2
    · have h2a : 2 * a = q + 1 := by
        rw [ha2, mul_comm]
        exact two_mul_div_two_of_even (by
          rcases hq with ⟨m, hm⟩
          use m + 1
          omega)
      have h2b : 2 * b = q - 1 := by
        rw [hb1, mul_comm]
        exact two_mul_div_two_of_even (by
          rcases hq with ⟨m, hm⟩
          use m
          omega)
      calc
        2 * a * (2 * b) = (q + 1) * (q - 1) := by rw [h2a, h2b]
        _ = q ^ 2 - 1 := by
          rcases hq with ⟨m, hm⟩
          rw [hm]
          have h : (2 * m + 1) ^ 2 = 2 * m * (2 * m + 2) + 1 := by ring
          calc
            (2 * m + 2) * (2 * m) = 2 * m * (2 * m + 2) := by ring
            _ = (2 * m * (2 * m + 2) + 1) - 1 := by omega
            _ = (2 * m + 1) ^ 2 - 1 := by rw [h]
    · exfalso
      have hEq : a = b := ha2.trans hb2.symm
      have hEven' : Even b := by simpa [hEq] using haEven
      rcases hbOdd with ⟨k, hk⟩
      rcases hEven' with ⟨l, hl⟩
      omega

/-- If `T` is the even quotient torus and `k'` the odd complementary half,
then `|E/Z(E)| = 2 q |T| k'`. -/
public theorem secondCase_linear_quotient_card_eq
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (torus : SecondCasePSL2QuotientTorusCard d K)
    (k' : ℕ)
    (hk' : k' = (Nat.card K - 1) / 2 ∨
      k' = (Nat.card K + 1) / 2)
    (hk'odd : Odd k') :
    Nat.card (d.E ⧸ Subgroup.center d.E) =
      2 * Nat.card K * Nat.card torus.T * k' := by
  have hqodd : Odd (Nat.card K) := by
    rcases torus.primePower with ⟨p, n, hp, hpodd, hn, hcard⟩
    rw [hcard]
    exact hpodd.pow
  have hQmodel : Nat.card (d.E ⧸ Subgroup.center d.E) = Nat.card (PSL2 K) :=
    Nat.card_congr torus.modelEquiv.some.toEquiv
  have hQformula : Nat.card (d.E ⧸ Subgroup.center d.E) =
      Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
    rw [hQmodel]
    exact psl2_card_formula K torus.primePower
  have hhalf : 2 * Nat.card torus.T * (2 * k') = Nat.card K ^ 2 - 1 :=
    complementary_half_product hqodd torus.T_card hk' torus.T_even hk'odd
  have hmul : Nat.card K * (Nat.card K ^ 2 - 1) =
      2 * (2 * Nat.card K * Nat.card torus.T * k') := by
    rw [← hhalf]
    ring
  calc
    Nat.card (d.E ⧸ Subgroup.center d.E) =
        Nat.card K * (Nat.card K ^ 2 - 1) / 2 := hQformula
    _ = (2 * (2 * Nat.card K * Nat.card torus.T * k')) / 2 := by rw [hmul]
    _ = 2 * Nat.card K * Nat.card torus.T * k' := by omega

end CFSG.GorensteinWalter
