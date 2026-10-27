module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Group.Subgroup.Finite

public import Mathlib.Algebra.Field.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

theorem coords_mul_self_eq_one {W : Type} [CommGroup W] {F ι : Type} [Field F] [CharP F 2]
    {W' : Subgroup W} (ψ : W' ≃* Multiplicative (ι → F)) (x : W') : x * x = 1 := by
  apply ψ.injective
  rw [map_mul, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul]
  have h : Multiplicative.toAdd (ψ x) + Multiplicative.toAdd (ψ x) = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero _
  rw [h, toAdd_one]

theorem exists_addSubgroup_image {W : Type} [CommGroup W] {V : Type} [AddCommGroup V]
    {W' : Subgroup W} (ψ : W' ≃* Multiplicative V) (E : Subgroup W) (hEW : E ≤ W') :
    ∃ S : AddSubgroup V,
      (∀ (x : W) (hx : x ∈ W'), x ∈ E ↔ Multiplicative.toAdd (ψ ⟨x, hx⟩) ∈ S) ∧
      Nat.card ↥S = Nat.card ↥E := by
  refine ⟨Subgroup.toAddSubgroup' ((E.subgroupOf W').map ψ.toMonoidHom), ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_toAddSubgroup', ofAdd_toAdd]
    exact Subgroup.mem_subgroupOf.symm.trans
      (Subgroup.mem_map_iff_mem (f := ψ.toMonoidHom) ψ.injective
        (K := E.subgroupOf W') (x := ⟨x, hx⟩)).symm
  · let T : Subgroup (Multiplicative V) := (E.subgroupOf W').map ψ.toMonoidHom
    change Nat.card ↥(Subgroup.toAddSubgroup' T) = Nat.card ↥E
    have h1 : Nat.card ↥(Subgroup.toAddSubgroup' T) = Nat.card ↥T :=
      Nat.card_congr
        { toFun := fun a => ⟨Multiplicative.ofAdd a.1,
            (Subgroup.mem_toAddSubgroup' T a.1).mp a.2⟩
          invFun := fun b => ⟨Multiplicative.toAdd b.1,
            (Subgroup.mem_toAddSubgroup' T (Multiplicative.toAdd b.1)).mpr
              (by simpa only [ofAdd_toAdd] using b.2)⟩
          left_inv := fun a => by ext; simp
          right_inv := fun b => by ext; simp }
    have h2 : Nat.card ↥T = Nat.card ↥(E.subgroupOf W') :=
      Subgroup.card_map_of_injective ψ.injective
    have h3 : Nat.card ↥(E.subgroupOf W') = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEW).toEquiv
    exact h1.trans (h2.trans h3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
