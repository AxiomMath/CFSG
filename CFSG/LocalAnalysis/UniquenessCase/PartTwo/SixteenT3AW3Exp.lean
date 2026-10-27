module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271TwistRel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16t_w3_mul_pow_three {H : Type} [Group H] [Finite H] {A : Subgroup H}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hA9 : Nat.card A = 9)
    {g : H} (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hg3 : g ^ 3 = 1) : ∀ a ∈ A, (a * g) ^ 3 = 1 := by
  intro a ha
  have hV : CFSG.Open.IsElemAbelian 3 A :=
    ⟨⟨⟨fun x y => Subtype.ext (hAc x x.2 y y.2)⟩⟩, hA3⟩
  have h1 := CFSG.HardMathSupport.Solomon.Coordinator.norm_triple_trivial hV hA9.le
    (φ := MulAut.conj g) ha (hgA a ha) (hgA _ (hgA a ha)) rfl rfl (by
      show g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ = a
      calc g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ = g * g * g * a * (g * g * g)⁻¹ := by
            simp only [mul_inv_rev, mul_assoc]
        _ = a := by rw [← pow_three', hg3, one_mul, inv_one, mul_one])
  calc (a * g) ^ 3 = a * (g * a * g⁻¹) * (g * (g * a * g⁻¹) * g⁻¹) * g ^ 3 := by
        rw [pow_three', pow_three']
        simp only [mul_assoc, inv_mul_cancel_left]
    _ = 1 := by rw [h1, hg3, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
