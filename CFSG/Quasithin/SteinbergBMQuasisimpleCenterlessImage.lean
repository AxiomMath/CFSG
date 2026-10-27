module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Quasithin.SteinbergBM

open Subgroup

theorem five_quasisimple_centerless_image {Q H : Type*} [Group Q] [Group H]
    (hQ : CFSG.IsQuasisimple Q) [IsSimpleGroup H] (hH : ∃ a b : H, a * b ≠ b * a)
    (α : Q →* H) (hα : Function.Surjective α) :
    α.ker = center Q ∧ ∃ e : Q ⧸ center Q ≃* H, ∀ q : Q, e q = α q := by
  have hker : α.ker = center Q := by
    refine le_antisymm ?_ fun z hz => ?_
    · rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ α.normal_ker with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := hH
        apply hab
        obtain ⟨a, rfl⟩ := hα a
        obtain ⟨b, rfl⟩ := hα b
        rw [α.mem_ker.mp (h ▸ mem_top a), α.mem_ker.mp (h ▸ mem_top b)]
      · exact h
    ·
      have hc : α z ∈ center H := by
        rw [mem_center_iff]
        intro h
        obtain ⟨q, rfl⟩ := hα h
        rw [← map_mul, ← map_mul, mem_center_iff.mp hz q]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H) with h | h
      · rw [h, mem_bot] at hc
        exact hc
      · exfalso
        obtain ⟨a, b, hab⟩ := hH
        exact hab (mem_center_iff.mp (h ▸ mem_top b) a)
  refine ⟨hker, (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα), fun q => ?_⟩
  rfl

end CFSG.Quasithin.SteinbergBM
