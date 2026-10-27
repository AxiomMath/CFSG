module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.OddIndexSylowTransfer

theorem exists_sylow_image
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Injective f)
    (hindex : ¬ p ∣ f.range.index) (S : Sylow p G) :
    ∃ T : Sylow p H, (T : Subgroup H) = (S : Subgroup G).map f := by
  have hi : ¬ p ∣ ((S : Subgroup G).map f).index := by
    rw [Subgroup.index_map_of_injective _ hf]
    intro h
    exact (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp h |>.elim S.not_dvd_index hindex
  exact ⟨(S.isPGroup'.map f).toSylow hi, rfl⟩

end FiveTransitive.OddIndexSylowTransfer

end CFSG
