module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

variable {G : Type*} [Group G]

theorem conjClosure_le_of_le {I H : Subgroup G} (h : I ≤ H) :
    CFSG.Quasithin.conjClosure I H ≤ H :=
  CFSG.Quasithin.conjClosure_le fun k hk z hz => H.mul_mem (H.mul_mem hk (h hz)) (H.inv_mem hk)

theorem isElemAbelian_conjClosure {I H : Subgroup G} (hI : IsElemAbelian 2 I)
    (hc : ∀ k ∈ H, ∀ a ∈ I, ∀ b ∈ I, a * (k * b * k⁻¹) = k * b * k⁻¹ * a) :
    IsElemAbelian 2 (CFSG.Quasithin.conjClosure I H) := by
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro _ ⟨h₁, hh₁, z₁, hz₁, rfl⟩ _ ⟨h₂, hh₂, z₂, hz₂, rfl⟩
    have h := hc (h₁⁻¹ * h₂) (H.mul_mem (H.inv_mem hh₁) hh₂) z₁ hz₁ z₂ hz₂
    calc h₁ * z₁ * h₁⁻¹ * (h₂ * z₂ * h₂⁻¹)
        = h₁ * (z₁ * (h₁⁻¹ * h₂ * z₂ * (h₁⁻¹ * h₂)⁻¹)) * h₁⁻¹ := by group
      _ = h₁ * (h₁⁻¹ * h₂ * z₂ * (h₁⁻¹ * h₂)⁻¹ * z₁) * h₁⁻¹ := by rw [h]
      _ = h₂ * z₂ * h₂⁻¹ * (h₁ * z₁ * h₁⁻¹) := by group
  · rintro _ ⟨h, hh, z, hz, rfl⟩
    have hz2 : z ^ 2 = 1 := hI.2 z hz
    rw [conj_pow, hz2]
    group

end CFSG.LocalAnalysis.WeakClosure81

end
