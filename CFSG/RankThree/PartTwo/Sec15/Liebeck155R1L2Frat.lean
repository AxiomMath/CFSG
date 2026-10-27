module

public import CFSG.RankThree.PartTwo.Sec15.MathUC155ThmC

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

theorem exists_normalizes_not_commute_of_frattini {P H : Type*} [Group P] [Finite P] [Group H]
    (ρ : P →* H) {p : ℕ} [Fact p.Prime] (Y₁ K₁ S : Subgroup P) (hKY : K₁ ≤ Y₁)
    (hKn : ∀ y ∈ Y₁, ∀ k ∈ K₁, y * k * y⁻¹ ∈ K₁) (hSK : S ≤ K₁) (hSp : IsPGroup p S)
    (hSmax : ∀ X : Subgroup P, X ≤ K₁ → IsPGroup p X → Nat.card X ≤ Nat.card S)
    (T : Subgroup H) (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hKT : ∀ k ∈ K₁, ρ k ∈ T)
    {y : P} (hy : y ∈ Y₁) (hyT : ¬ ∀ t ∈ T, ρ y * t = t * ρ y) :
    ∃ w ∈ Y₁, (∀ s ∈ S, w * s * w⁻¹ ∈ S) ∧ ¬ ∀ t ∈ T, ρ w * t = t * ρ w := by
  obtain ⟨b, hb, w, hw, hwS, hyeq⟩ :=
    CFSG.RankThree.PartTwo.Sec15.MathUC155ThmC.exists_mul_normalizes_of_card_max
      Y₁ K₁ S hKY hKn hSK hSp hSmax y hy
  refine ⟨w, hw, hwS, fun hcomm => hyT fun t ht => ?_⟩
  have hbT : ρ b ∈ T := hKT b hb
  have h1 : ρ b * t = t * ρ b := hTc (ρ b) hbT t ht
  have h2 : ρ w * t = t * ρ w := hcomm t ht
  rw [hyeq, map_mul]
  calc ρ b * ρ w * t = ρ b * (ρ w * t) := mul_assoc _ _ _
    _ = ρ b * (t * ρ w) := by rw [h2]
    _ = ρ b * t * ρ w := (mul_assoc _ _ _).symm
    _ = t * ρ b * ρ w := by rw [h1]
    _ = t * (ρ b * ρ w) := mul_assoc _ _ _

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
