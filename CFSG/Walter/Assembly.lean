module

public import CFSG.Walter.SimpleCase
public import CFSG.Open.Defs
public import CFSG.Open.WalterAbelianSylowTwoMilestoneDefs

public section

namespace CFSG.Walter

open scoped MatrixGroups

@[expose] def JRHyp : Prop := ∀ (G : Type) [Group G] [Finite G], IsTypeJR G →
  (∃ a b : G, a * b ≠ b * a) →
  (∃ m : ℕ, 1 ≤ m ∧ Nat.card G = CFSG.Open.ordRee (3 ^ (2 * m + 1))) ∨
  Nonempty (G ≃* CFSG.Open.walterJ1)

open Matrix in
theorem walter_order_form
    (hB : BenderHyp) (hJ : JRHyp) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    (hP : IsMulCommutative (P : Subgroup G)) :
    (∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nat.card G = CFSG.Open.ordRee (3 ^ (2 * m + 1))) ∨
    Nonempty (G ≃* CFSG.Open.walterJ1) := by
  have hab : HasAbelianSylowTwo G := hasAbelianSylowTwo_of_sylow P hP
  have hSC := simpleCaseHyp_of_benderHyp hB
  rcases hSC G inferInstance hnonab hab
      (fun H _ => isAStar_of_hasAbelianSylowTwo hSC (hab.subgroup H)) with hL2 | hJR
  · rcases hL2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hJ G hJR hnonab with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

end CFSG.Walter
