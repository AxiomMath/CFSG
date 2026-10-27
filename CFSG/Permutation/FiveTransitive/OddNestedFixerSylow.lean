module

public import CFSG.Permutation.FiveTransitive.OddIndexSylowTransfer
public import CFSG.Permutation.FiveTransitive.GenericSylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.OddNestedFixerSylow

open MulAction GenericSylowFixedAction

private theorem relative_index
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (s t : Set X) (hs : s.ncard = 4) (ht : t.ncard = 5) (hst : s ⊆ t) :
    (fixingSubgroup G t).relIndex (fixingSubgroup G s) = Nat.card X - 4 := by
  have hn : 5 ≤ Nat.card X := by
    rw [← ht]
    exact Set.ncard_le_card t
  let _ : IsMultiplyPretransitive G X 5 := h5
  have h4 : IsMultiplyPretransitive G X 4 :=
    isMultiplyPretransitive_of_le (by omega : 4 ≤ 5) hn
  have hi4 := h4.index_of_fixingSubgroup_mul hs
  have hi5 := h5.index_of_fixingSubgroup_mul ht
  have hle : fixingSubgroup G t ≤ fixingSubgroup G s := by
    intro g hg
    exact (mem_fixingSubgroup_iff G).mpr (fun x hx =>
      (mem_fixingSubgroup_iff G).mp hg x (hst hx))
  have hi := Subgroup.relIndex_mul_index hle
  have hfact : (Nat.card X - 4).factorial =
      (Nat.card X - 4) * (Nat.card X - 5).factorial := by
    conv_lhs => rw [show Nat.card X - 4 = (Nat.card X - 5) + 1 by omega]
    rw [Nat.factorial_succ]
    congr 1
    omega
  rw [hfact] at hi4
  apply Nat.eq_of_mul_eq_mul_right (mul_pos
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := fixingSubgroup G s)))
    (Nat.factorial_pos (Nat.card X - 5)))
  calc
    (fixingSubgroup G t).relIndex (fixingSubgroup G s) *
        ((fixingSubgroup G s).index * (Nat.card X - 5).factorial) =
      (fixingSubgroup G t).index * (Nat.card X - 5).factorial := by rw [← mul_assoc, hi]
    _ = (Nat.card X).factorial := hi5
    _ = (Nat.card X - 4) *
      ((fixingSubgroup G s).index * (Nat.card X - 5).factorial) := by rw [← hi4]; ring

theorem exists_four_fixer_sylow
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5) (hodd : Odd (Nat.card X))
    (s t : Set X) (hs : s.ncard = 4) (ht : t.ncard = 5) (hst : s ⊆ t)
    (S : Sylow 2 (fixingSubgroup G t)) :
    ∃ T : Sylow 2 (fixingSubgroup G s), sylowImage G X s T = sylowImage G X t S := by
  have hle : fixingSubgroup G t ≤ fixingSubgroup G s := by
    intro g hg
    exact (mem_fixingSubgroup_iff G).mpr (fun x hx =>
      (mem_fixingSubgroup_iff G).mp hg x (hst hx))
  let f := Subgroup.inclusion hle
  have hi : ¬ 2 ∣ f.range.index := by
    rw [Subgroup.inclusion_range]
    change ¬ 2 ∣ (fixingSubgroup G t).relIndex (fixingSubgroup G s)
    rw [relative_index G X h5 s t hs ht hst]
    have hn := Set.ncard_le_card t
    rw [ht] at hn
    have ho := Nat.odd_iff.mp hodd
    omega
  obtain ⟨T, hT⟩ := OddIndexSylowTransfer.exists_sylow_image f
    (Subgroup.inclusion_injective hle) hi S
  refine ⟨T, ?_⟩
  change (T : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = _
  rw [hT, Subgroup.map_map]
  rfl

end FiveTransitive.OddNestedFixerSylow

end CFSG
