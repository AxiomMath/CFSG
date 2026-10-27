module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.SBd19F

theorem le_of_isPerfect_of_index_two {G : Type*} [Group G] {N P : Subgroup G}
    (hN : N.index = 2) (hP : Group.IsPerfect P) : P ≤ N := by
  have : N.Normal := Subgroup.normal_of_index_eq_two hN
  have hcard : Nat.card (G ⧸ N) = 2 := by rwa [← Subgroup.index_eq_card]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hcard
  have := hP
  let f : P →* G ⧸ N := (QuotientGroup.mk' N).comp P.subtype
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : IsMulCommutative f.range := inferInstance
  have : Subsingleton f.range := inferInstance
  intro x hx
  have hfx : f ⟨x, hx⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict ⟨x, hx⟩) 1)
  exact (QuotientGroup.eq_one_iff x).mp hfx

theorem isPerfect_comap_of_le_range {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {Q : Subgroup H} (hQ : Q ≤ φ.range) (hP : Group.IsPerfect Q) :
    Group.IsPerfect (Q.comap φ) ∧ Nat.card (Q.comap φ) = Nat.card Q := by
  have hmap : (Q.comap φ).map φ = Q := Subgroup.map_comap_eq_self hQ
  let e : Q.comap φ ≃* Q :=
    (Subgroup.equivMapOfInjective (Q.comap φ) φ hφ).trans (MulEquiv.subgroupCongr hmap)
  have := hP
  exact ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
    Nat.card_congr e.toEquiv⟩

theorem le_of_isPerfect_of_relindex_two {G : Type*} [Group G] {P N X : Subgroup G} (hPX : P ≤ X)
    (hN : (N.subgroupOf X).index = 2) (hP : Group.IsPerfect P) : P ≤ N := by
  have hX : P ≤ X.subtype.range := by rwa [Subgroup.range_subtype]
  have hle := le_of_isPerfect_of_index_two hN
    (isPerfect_comap_of_le_range X.subtype_injective hX hP).1
  intro x hx
  exact Subgroup.mem_subgroupOf.mp
    (hle (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hPX hx⟩ : X) ∈ P.subgroupOf X))

end CFSG.Quasithin.SBd19F
