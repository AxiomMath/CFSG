module

public import CFSG.GroupTheory.MulAutTrivialOnSubgroup

@[expose] public section

namespace CFSG

variable {B : Type} [Group B] [Finite B]

theorem MulAut.eq_on_zpowers_of_commute_card_three
    {Y₂ : Subgroup (MulAut B)} {t : MulAut B} {b₁ : B}
    (hodd : Odd (Nat.card Y₂))
    (hcard : Nat.card (Subgroup.zpowers b₁) = 3)
    (hcomm : ∀ y : MulAut B, y ∈ Y₂ → y * t = t * y)
    (himage : ∀ x : B, x⁻¹ * t x ∈ Subgroup.zpowers b₁)
    (hcover : ∀ c : B, c ∈ Subgroup.zpowers b₁ → ∃ x : B, x⁻¹ * t x = c) :
    ∀ (y : MulAut B), y ∈ Y₂ → y b₁ = b₁ := by
  have hmem : ∀ (z : MulAut B), z ∈ Y₂ → ∀ c : B, c ∈ Subgroup.zpowers b₁ →
      z c ∈ Subgroup.zpowers b₁ := by
    intro z hz c hc
    obtain ⟨x, rfl⟩ := hcover c hc
    have hzx : z (x⁻¹ * t x) = (z x)⁻¹ * t (z x) := by
      rw [map_mul, map_inv]
      congr 1
      calc
        z (t x) = (z * t) x := (MulAut.mul_apply B z t x).symm
        _ = (t * z) x := by rw [hcomm z hz]
        _ = t (z x) := MulAut.mul_apply B t z x
    rw [hzx]
    exact himage (z x)
  have hpres : ∀ y : MulAut B, y ∈ Y₂ →
      Subgroup.map y (Subgroup.zpowers b₁) = Subgroup.zpowers b₁ := by
    intro y hy
    apply le_antisymm
    · intro c hc
      rw [Subgroup.mem_map] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      exact hmem y hy a ha
    · intro c hc
      rw [Subgroup.mem_map]
      refine ⟨y⁻¹ c, hmem y⁻¹ (Y₂.inv_mem hy) c hc, by simp⟩
  intro y hy
  exact MulAut.act_trivial_of_preserves_card_three (Y := Y₂) (C := Subgroup.zpowers b₁)
    hodd hcard hpres y hy b₁ (Subgroup.mem_zpowers b₁)

end CFSG
