module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinDataComplete
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCountEquations14
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-!
# Derived numerical facts for the first-case count

The arithmetic consequences of restriction (7) that do not need the coset
pair-count are isolated here: `|K| = |U| = 3` once the odd core has order
three, and `b₄ ≠ 0` follows from identities (8) and (9) together with
`K ≠ 1`.
-/

/-- A nontrivial Hall subgroup of `F(U)` has the full order of `U` once
`|U| = 3`. -/
public theorem firstCase_klein_K_card_eq_three_of_U_card_three
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {K : Subgroup G}
    (hKHall : IsHallIn K c.FU) (hKne : K ≠ ⊥)
    (hUcard : Nat.card c.U = 3) :
    Nat.card K = 3 := by
  have hKleU : K ≤ c.U := hKHall.1.trans (fittingSubgroupOf_le c.U)
  have hdvd : Nat.card K ∣ Nat.card c.U := Subgroup.card_dvd_of_le hKleU
  rw [hUcard] at hdvd
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hne1 : Nat.card K ≠ 1 := by
    intro hcard
    exact hKne (Subgroup.eq_bot_of_card_eq K hcard)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact False.elim (hne1 h1)
  · exact h3

/-- If `b₄ = 0`, identities (8) and (9) force `k = 1`, contradicting
`K ≠ 1`. -/
public theorem firstCase_klein_b4_ne_zero_of_equations
    (k b0 b1 b2 b4 : ℕ)
    (h8 : 3 * b4 + b2 = 6 * k ^ 2)
    (h9 : 6 * k + b4 = 3 * b0 + 2 * b1 + b2)
    (hkge2 : 2 ≤ k) :
    b4 ≠ 0 := by
  intro hb4
  have hb2 : b2 = 6 * k ^ 2 := by omega
  have hmain : 6 * k = 3 * b0 + 2 * b1 + 6 * k ^ 2 := by omega
  have hle : 6 * k ^ 2 ≤ 6 * k := by omega
  have hk1 : k ≤ 1 := by nlinarith
  omega

end CFSG.GorensteinWalter
