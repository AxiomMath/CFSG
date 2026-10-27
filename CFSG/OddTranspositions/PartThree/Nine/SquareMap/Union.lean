module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddTranspositions.PartThree.Nine

theorem map_conj_eq_or_eq_of_involutions_union {G : Type*} [Group G] [Finite G]
    {V A B : Subgroup G} (hAV : A ≤ V) (hA2 : ∀ a ∈ A, a * a = 1)
    (hcard : Nat.card A = Nat.card B) (hI : ∀ v ∈ V, v * v = 1 → v ∈ A ∨ v ∈ B) {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    A.map (MulAut.conj x).toMonoidHom = A ∨ A.map (MulAut.conj x).toMonoidHom = B := by
  have hleV : A.map (MulAut.conj x).toMonoidHom ≤ V := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    simpa using (Subgroup.mem_normalizer_iff.1 hx a).1 (hAV ha)
  have hsq : ∀ y ∈ A.map (MulAut.conj x).toMonoidHom, y * y = 1 := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [← map_mul, hA2 a ha, map_one]
  have hsub : (A.map (MulAut.conj x).toMonoidHom : Set G) ⊆ (A : Set G) ∪ (B : Set G) :=
    fun y hy => hI y (hleV hy) (hsq y hy)
  have hcard' : Nat.card (A.map (MulAut.conj x).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  rcases SubgroupClass.subset_union.1 hsub with hle | hle
  · left
    exact Subgroup.eq_of_le_of_card_ge hle hcard'.ge
  · right
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard']; exact le_of_eq hcard.symm)

end CFSG.OddTranspositions.PartThree.Nine
