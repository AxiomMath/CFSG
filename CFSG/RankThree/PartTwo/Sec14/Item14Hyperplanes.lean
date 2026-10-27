module

public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.RankThree.PartTwo.Sec12.Coordinates

public section

namespace CFSG.RankThree.PartTwo.Sec14

@[expose] def dot3 (v w : Fin 3 → ZMod 3) : ZMod 3 := v 0 * w 0 + v 1 * w 1 + v 2 * w 2

@[expose] def dotKer (v : Fin 3 → ZMod 3) : Subgroup (Multiplicative (Fin 3 → ZMod 3)) where
  carrier := {w | dot3 v (Multiplicative.toAdd w) = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, toAdd_mul, dot3, Pi.add_apply] at ha hb ⊢
    linear_combination ha + hb
  one_mem' := by simp [dot3]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, toAdd_inv, dot3, Pi.neg_apply] at ha ⊢
    linear_combination -ha

instance (v : Fin 3 → ZMod 3) : DecidablePred (· ∈ dotKer v) := fun w =>
  inferInstanceAs (Decidable (dot3 v (Multiplicative.toAdd w) = 0))

@[expose] def rep13 : Fin 13 → Fin 3 → ZMod 3 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 2, 0], ![1, 0, 1], ![1, 0, 2],
    ![0, 1, 1], ![0, 1, 2], ![1, 1, 1], ![1, 1, 2], ![1, 2, 1], ![1, 2, 2]]

theorem card_dotKer_rep13 (i : Fin 13) : Fintype.card (dotKer (rep13 i)) = 9 := by
  revert i
  decide

theorem dotKer_rep13_injective : Function.Injective fun i => dotKer (rep13 i) := by
  intro i j h
  by_contra hij
  have key : ∀ i j : Fin 13, i ≠ j →
      ∃ w : Multiplicative (Fin 3 → ZMod 3), w ∈ dotKer (rep13 i) ∧ w ∉ dotKer (rep13 j) := by
    decide
  obtain ⟨w, hw, hw'⟩ := key i j hij
  exact hw' (by simpa [h] using hw)


variable {G : Type*} [Group G] [Finite G]

theorem exists_hyperplanes_thirteen {A : Subgroup G} (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) :
    ∃ f : Fin 13 → Subgroup G, Function.Injective f ∧ ∀ i, IsHyperplane A (f i) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec12.exists_coords hA.1 (n := 3) (by rw [hA.2]; norm_num)
  refine ⟨fun i => ((dotKer (rep13 i)).map e.toMonoidHom).map A.subtype, ?_, fun i => ?_⟩
  · intro i j h
    apply dotKer_rep13_injective
    have h1 := Subgroup.map_injective A.subtype_injective h
    exact Subgroup.map_injective e.injective h1
  · have h9 : Nat.card ↥(dotKer (rep13 i)) = 9 := by
      rw [Nat.card_eq_fintype_card, card_dotKer_rep13]
    refine ⟨Subgroup.map_subtype_le _, ?_⟩
    rw [Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.card_map_of_injective e.injective, h9, hA.2]

theorem false_of_injOn_hyperplanes {A : Subgroup G} (hA : CFSG.RankThree.PartTwo.Late.IsE27 A)
    {S : Set (Subgroup G)} (hS : S.ncard ≤ 12) (g : Subgroup G → Subgroup G)
    (hg : ∀ B, IsHyperplane A B → g B ∈ S)
    (hinj : ∀ B B', IsHyperplane A B → IsHyperplane A B' → g B = g B' → B = B') : False := by
  obtain ⟨f, hf, hfA⟩ := exists_hyperplanes_thirteen hA
  have hinj' : Function.Injective (g ∘ f) := fun i j h => hf (hinj _ _ (hfA i) (hfA j) h)
  have hsub : Set.range (g ∘ f) ⊆ S := by
    rintro _ ⟨i, rfl⟩
    exact hg _ (hfA i)
  have h13 : (Set.range (g ∘ f)).ncard = 13 := by
    rw [Set.ncard_range_of_injective hinj', Nat.card_eq_fintype_card, Fintype.card_fin]
  have := Set.ncard_le_ncard hsub (Set.toFinite S)
  omega

end CFSG.RankThree.PartTwo.Sec14
