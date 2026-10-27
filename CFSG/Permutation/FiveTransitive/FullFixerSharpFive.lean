module

public import CFSG.Permutation.FiveTransitive.FullFixerFixedAction
public import CFSG.Permutation.FiveTransitive.SharpFourCentralizer
public import CFSG.Permutation.FiveTransitive.Helpers
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace FiveTransitive.FullFixerSharpFive

open MulAction FixedNormalizerAction

theorem sharp_image
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5) (s : Set X) (hs : s.ncard = 5) :
    IsMultiplyPretransitive (Image (X := X) (fixingSubgroup G s))
        (Fixed (X := X) (fixingSubgroup G s)) 5 ∧
    5 ≤ Nat.card (Fixed (X := X) (fixingSubgroup G s)) ∧
    Nat.card (Image (X := X) (fixingSubgroup G s)) =
      (Nat.card (Fixed (X := X) (fixingSubgroup G s))).descFactorial 5 := by
  classical
  let H := fixingSubgroup G s
  let F := Fixed (X := X) H
  let J := Image (X := X) H
  let _ : Fintype F := Fintype.ofFinite _
  let sF : Set F := {x | (x : X) ∈ s}
  have hN5 := FullFixerFixedAction.normalizer_multiply h5 s hs
  have hJ5 : IsMultiplyPretransitive J F 5 := by
    rw [isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g,hg⟩ := hN5.exists_smul_eq a b
    exact ⟨⟨toPermHom (Normalizer H) F g,⟨g,rfl⟩⟩,hg⟩
  have hsF : s ⊆ (F : Set X) := by
    change s ⊆ Fixed (X := X) H
    rw [fixed_eq]
    intro x hx h
    exact (mem_fixingSubgroup_iff G).mp h.property x hx
  let e : s ≃ sF :=
    { toFun := fun x => ⟨⟨x.val,hsF x.property⟩,x.property⟩
      invFun := fun x => ⟨x.val.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hbase : sF.ncard = 5 := by
    rw [← Nat.card_coe_set_eq,← Nat.card_congr e, Nat.card_coe_set_eq,hs]
  have hsize : 5 ≤ Nat.card F := by
    rw [Nat.card_coe_set_eq]
    exact hs ▸ Set.ncard_le_ncard hsF
  have htrans : IsMultiplyPretransitive J F sF.ncard := by rw [hbase]; exact hJ5
  have hi := htrans.index_of_fixingSubgroup_eq sF
  have hbot : fixingSubgroup J sF = ⊥ := FullFixerFixedAction.image_base_fixer_eq_bot s
  rw [hbot,Subgroup.index_bot,hbase] at hi
  refine ⟨hJ5,hsize,?_⟩
  simpa only [Nat.descFactorial_eq_factorial_mul_choose,Nat.mul_comm] using hi

theorem fixed_degree_cases
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5) (s : Set X) (hs : s.ncard = 5) :
    let m := Nat.card (Fixed (X := X) (fixingSubgroup G s))
    m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 12 := by
  classical
  let H := fixingSubgroup G s
  let F := Fixed (X := X) H
  let J := Image (X := X) H
  let _ : Fintype F := Fintype.ofFinite _
  let _ : Fintype J := Fintype.ofFinite _
  obtain ⟨hJ5,hsize,hsharp⟩ := sharp_image h5 s hs
  change IsMultiplyPretransitive J F 5 at hJ5
  change 5 ≤ Nat.card F at hsize
  change Nat.card J = (Nat.card F).descFactorial 5 at hsharp
  have hle : Nat.card F ≤ 12 := by
    simpa only [Nat.card_eq_fintype_card] using
      FiveTransitive.Research.SharpFourDegreeCompletion.sharp_five_degree_le_twelve hJ5
        (by simpa only [Nat.card_eq_fintype_card] using hsharp)
  change Nat.card F = 5 ∨ Nat.card F = 6 ∨ Nat.card F = 7 ∨ Nat.card F = 12
  by_contra hn
  have hm : Nat.card F = 8 ∨ Nat.card F = 9 ∨ Nat.card F = 10 ∨ Nat.card F = 11 := by omega
  have hc := Helpers.classification_of_five_transitive_of_card_le_eleven J F
    (by simpa only [Nat.card_eq_fintype_card] using hsize)
    (by simpa only [Nat.card_eq_fintype_card] using (show Nat.card F ≤ 11 by omega))
    (by
      intro a b ha hb
      obtain ⟨g,hg⟩ := hJ5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ F) ⟨b,hb⟩
      exact ⟨g,fun i => DFunLike.congr_fun hg i⟩)
  rw [← Nat.card_eq_fintype_card (α := J),← Nat.card_eq_fintype_card (α := F),hsharp] at hc
  rcases hm with hm | hm | hm | hm <;> rw [hm] at hc <;>
    norm_num [Nat.factorial,Nat.descFactorial] at hc

end FiveTransitive.FullFixerSharpFive

end CFSG
