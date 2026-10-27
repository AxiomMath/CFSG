module

public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGRCArith

public section

namespace CFSG.StandardType

theorem ggRC_small_of_card
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (ML : CoxeterMatrix Λ) (hWL : GGIsWeylMatrix ML) (h8 : 8 ≤ Fintype.card Λ)
    {Nj NB : ℕ} (hNB : NB = p ^ (Fintype.card Λ + 1))
    (hjoin : Nj ≤ NB * ((p - 1) * 6 * Nat.card ML.Group)) :
    8 * Nj < p ^ ((Fintype.card Λ + 1) * Fintype.card Λ / 2) := by
  have hle : 2 ^ Fintype.card Λ * (Fintype.card Λ).factorial ≤
      2 ^ (Fintype.card Λ + 1) * (Fintype.card Λ + 1).factorial :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
      (Nat.factorial_le (Nat.le_succ _))
  have hW' : Nat.card ML.Group ≤
        2 ^ (Fintype.card Λ + 1) * (Fintype.card Λ + 1).factorial ∨
      (Fintype.card Λ + 1 = 9 ∧ Nat.card ML.Group = 696729600) := by
    rcases ggRC_card_weyl_le ML hWL h8 with h | ⟨hcard8, hord⟩
    · exact Or.inl (le_trans h hle)
    · exact Or.inr ⟨by omega, hord⟩
  have harith := ggRC_arith hp hp2 (by omega : 9 ≤ Fintype.card Λ + 1) hW'
  have hjoin' : Nj ≤ p ^ (Fintype.card Λ + 1) * ((p - 1) * 6 * Nat.card ML.Group) := by
    rw [hNB] at hjoin
    exact hjoin
  calc
    8 * Nj ≤ 8 * (p ^ (Fintype.card Λ + 1) * ((p - 1) * 6 * Nat.card ML.Group)) :=
      Nat.mul_le_mul_left 8 hjoin'
    _ < p ^ ((Fintype.card Λ + 1) * ((Fintype.card Λ + 1) - 1) / 2) := harith
    _ = p ^ ((Fintype.card Λ + 1) * Fintype.card Λ / 2) := by
      rw [Nat.add_sub_cancel]

end CFSG.StandardType
