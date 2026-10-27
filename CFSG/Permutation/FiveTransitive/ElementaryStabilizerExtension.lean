module

public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup

public section

namespace CFSG

namespace FiveTransitive.ElementaryStabilizerExtension

theorem exists_extension
    {G : Type*} [Group G] (B : Subgroup G) (D : Subgroup B)
    (a : G) (haB : a ∈ B) (ha2 : a ^ 2 = 1)
    (hcomm : ∀ d : D, Commute a d.val.val)
    (hD2 : ∀ d : D, d ^ 2 = 1) (hDcomm : IsMulCommutative D)
    (hdiv : 8 ∣ Nat.card D) :
    ∃ K : Subgroup G,
      K = Subgroup.closure (insert a (D.map B.subtype : Set G)) ∧
      K ≤ B ∧ a ∈ K ∧ D.map B.subtype ≤ K ∧
      IsPGroup 2 K ∧ (∀ k : K, k ^ 2 = 1) ∧ IsMulCommutative K ∧ 8 ∣ Nat.card K := by
  let T := D.map B.subtype
  let K := Subgroup.closure (insert a (T : Set G))
  have hKB : K ≤ B := (Subgroup.closure_le B).mpr (by
    intro g hg
    rcases hg with rfl | ⟨d, hd, rfl⟩
    · exact haB
    · exact d.property)
  have haK : a ∈ K := Subgroup.subset_closure (Set.mem_insert a _)
  have hTK : T ≤ K := fun g hg => Subgroup.subset_closure (Set.mem_insert_of_mem a hg)
  have hc : (insert a (T : Set G)).Pairwise Commute := by
    intro g hg h hh hgh
    rcases hg with rfl | ⟨d, hd, rfl⟩ <;> rcases hh with rfl | ⟨e, he, rfl⟩
    · exact Commute.refl _
    · exact hcomm ⟨e, he⟩
    · exact (hcomm ⟨d, hd⟩).symm
    · exact congrArg (fun k : D => k.val.val)
        ((isMulCommutative_iff.mp hDcomm) ⟨d, hd⟩ ⟨e, he⟩)
  have hs : ∀ g ∈ insert a (T : Set G), g ^ 2 = 1 := by
    intro g hg
    rcases hg with rfl | ⟨d, hd, rfl⟩
    · exact ha2
    · exact congrArg (fun k : D => k.val.val) (hD2 ⟨d, hd⟩)
  obtain ⟨hp, hsq⟩ := ThreeSwapTwoGroup.closure_two_group _ hc hs
  have habel : IsMulCommutative K := Subgroup.isMulCommutative_closure hc
  have hcard : Nat.card T = Nat.card D := Subgroup.card_map_of_injective Subtype.val_injective
  have hdivK : 8 ∣ Nat.card K := by
    apply dvd_trans _ (Subgroup.card_dvd_of_le hTK)
    rwa [hcard]
  exact ⟨K, rfl, hKB, haK, hTK, hp, hsq, habel, hdivK⟩

end FiveTransitive.ElementaryStabilizerExtension

end CFSG
