module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14Base
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

theorem frattini_G {H M P : Subgroup G} (hMH : M ≤ H) (hMn : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M)
    (hP : IsSylowOf 3 P M) : ∀ x ∈ H, ∃ m ∈ M, ∃ n ∈ H ⊓ Nor P, x = m * n := by
  intro x hx
  set P' : Subgroup G := P.map (MulAut.conj x).toMonoidHom with hP'
  have hP'M : P' ≤ M := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hMn x hx y (hP.1 hy)
  have hP'p : IsPGroup 3 P' := hP.2.1.map _
  obtain ⟨k, hkM, hk⟩ := FF79.L14.exists_conj_le_sylowOf hP hP'M hP'p
  have hle : P.map (MulAut.conj (k * x)).toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    have := hk (x * y * x⁻¹) ⟨y, hy, by simp [MulAut.conj_apply]⟩
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hcard : Nat.card P ≤ Nat.card (P.map (MulAut.conj (k * x)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (k * x)).injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hkx : k * x ∈ Nor P := by
    rw [Nor, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hle ⟨z, hz, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · intro hz
      rw [← heq] at hz
      obtain ⟨y, hy, hyz⟩ := hz
      have : y = z := by
        have h1 : (k * x) * y * (k * x)⁻¹ = (k * x) * z * (k * x)⁻¹ := by
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hyz
        exact mul_left_cancel (mul_right_cancel h1)
      exact this ▸ hy
  refine ⟨k⁻¹, inv_mem hkM, k * x, Subgroup.mem_inf.2 ⟨H.mul_mem (hMH hkM) hx, hkx⟩, by group⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
