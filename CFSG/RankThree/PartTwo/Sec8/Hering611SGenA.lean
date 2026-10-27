module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_mem_coset {B N : Subgroup G} (hB : IsPGroup 3 B)
    (hN3 : ¬ 3 ∣ Nat.card N) (hBN : B ≤ Subgroup.normalizer (N : Set G)) {y : G}
    (hy : ∀ b ∈ B, y⁻¹ * (b * y * b⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ b ∈ B, b * (y * n) * b⁻¹ = y * n := by
  have hmem : ∀ b ∈ B, ∀ n ∈ N, y⁻¹ * (b * (y * n) * b⁻¹) ∈ N := by
    intro b hb n hn
    have hconj : b * n * b⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hBN hb) n).mp hn
    have hfac : y⁻¹ * (b * (y * n) * b⁻¹) = (y⁻¹ * (b * y * b⁻¹)) * (b * n * b⁻¹) := by
      group
    rw [hfac]
    exact N.mul_mem (hy b hb) hconj
  letI : MulAction ↥B ↥N :=
    { smul := fun b n => ⟨y⁻¹ * ((b : G) * (y * (n : G)) * (b : G)⁻¹), hmem b b.2 n n.2⟩
      one_smul := fun n => Subtype.ext (by
        show y⁻¹ * ((1 : G) * (y * (n : G)) * (1 : G)⁻¹) = (n : G)
        group)
      mul_smul := fun b₁ b₂ n => Subtype.ext (by
        show y⁻¹ * ((b₁ : G) * (b₂ : G) * (y * (n : G)) * ((b₁ : G) * (b₂ : G))⁻¹)
          = y⁻¹ * ((b₁ : G) * (y * (y⁻¹ * ((b₂ : G) * (y * (n : G)) * (b₂ : G)⁻¹))) *
            (b₁ : G)⁻¹)
        group) }
  obtain ⟨n, hn⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card ↥N hN3
  have hfix : ∀ b : ↥B, b • n = n := MulAction.mem_fixedPoints.mp hn
  refine ⟨(n : G), n.2, fun b hb => ?_⟩
  have h : y⁻¹ * (b * (y * (n : G)) * b⁻¹) = n := congrArg Subtype.val (hfix ⟨b, hb⟩)
  calc b * (y * n) * b⁻¹ = y * (y⁻¹ * (b * (y * n) * b⁻¹)) := (mul_inv_cancel_left _ _).symm
    _ = y * n := by rw [h]

end CFSG.RankThree.PartTwo.Sec8.Hering611
