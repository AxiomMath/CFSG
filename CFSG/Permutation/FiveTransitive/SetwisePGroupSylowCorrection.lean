module

public import CFSG.Permutation.FiveTransitive.PGroupSylowSimultaneousCorrection
public import CFSG.Permutation.FiveTransitive.SetwiseSylowNormalizer

public section

namespace CFSG

namespace FiveTransitive.SetwisePGroupSylowCorrection

open MulAction

theorem exists_correction
    {G X : Type*} [Group G] [Finite G] [MulAction G X] {p : ℕ} [Fact p.Prime]
    (s : Set X) (P : Sylow p (fixingSubgroup G s))
    (H : Subgroup G) (hH : IsPGroup p H)
    (hpreserves : ∀ h : H, ∀ y : X, y ∈ s ↔ h.val • y ∈ s) :
    ∃ k : fixingSubgroup G s, ∀ h : H,
      k.val * h.val * k.val⁻¹ ∈ Subgroup.normalizer
        (((P : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype) : Set G) ∧
      ∀ y ∈ s, (k.val * h.val * k.val⁻¹) • y = h.val • y := by
  have hN : H ≤ Subgroup.normalizer (fixingSubgroup G s : Set G) := by
    intro h hh
    exact SetwiseSylowNormalizer.normalizes_fixer s h (hpreserves ⟨h, hh⟩)
  obtain ⟨k, hk⟩ := PGroupSylowSimultaneousCorrection.exists_correction
    (fixingSubgroup G s) H hH hN P
  refine ⟨k, ?_⟩
  intro h
  refine ⟨hk h, ?_⟩
  intro y hy
  have hinv : k.val⁻¹ • y = y :=
    (mem_fixingSubgroup_iff G).mp ((fixingSubgroup G s).inv_mem k.property) y hy
  rw [mul_smul, mul_smul, hinv]
  exact (mem_fixingSubgroup_iff G).mp k.property _ ((hpreserves h y).mp hy)

end FiveTransitive.SetwisePGroupSylowCorrection

end CFSG
