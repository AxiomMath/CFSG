module

public import CFSG.RankThree.PartOne.KLR.CoreGroup

public section

namespace CFSG.RankThree.PartOne.KLR

theorem noSolvableRadical_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {P : Subgroup G} (hP : NoSolvableRadical P) :
    NoSolvableRadical (P.map f) := by
  intro N hN hnorm hsol
  set N' : Subgroup G := N.comap f ⊓ P with hN'
  have hNN' : N'.map f = N := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, _⟩, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hN hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have hN'sol : Group.IsSolvable N' := by
    let g : N' →* N := (f.comp N'.subtype).codRestrict N fun x => by
      rw [← hNN']
      exact ⟨x, x.2, rfl⟩
    have hg : Function.Injective g := fun x y h =>
      Subtype.ext (hf (congrArg Subtype.val h))
    exact Group.isSolvable_of_isSolvable_injective hg
  have hnorm' : ∀ u ∈ P, ∀ v ∈ N', u * v * u⁻¹ ∈ N' := by
    intro u hu v hv
    refine ⟨?_, ?_⟩
    · show f (u * v * u⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hnorm _ ⟨u, hu, rfl⟩ _ hv.1
    · exact P.mul_mem (P.mul_mem hu hv.2) (P.inv_mem hu)
  have h1 : N' = ⊥ := hP N' inf_le_right hnorm' hN'sol
  rw [← hNN', h1, Subgroup.map_bot]

theorem noSolvableRadical_of_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {P : Subgroup G} (hP : NoSolvableRadical (P.map f)) :
    NoSolvableRadical P := by
  intro N hN hnorm hsol
  have hsol' : Group.IsSolvable (N.map f) :=
    Group.isSolvable_of_surjective (f := f.subgroupMap N) (f.subgroupMap_surjective N)
  have h1 : N.map f = ⊥ := by
    refine hP (N.map f) (Subgroup.map_mono hN) ?_ hsol'
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    refine ⟨u * v * u⁻¹, hnorm u hu v hv, ?_⟩
    simp
  exact (Subgroup.map_eq_bot_iff_of_injective N hf).1 h1

theorem noSolvableRadical_top {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ¬ Group.IsSolvable X) : NoSolvableRadical (⊤ : Subgroup X) :=
  noSolvableRadical_of_mulEquiv hX (Subgroup.topEquiv (G := X))

theorem noSolvableRadical_range {X G : Type*} [Group X] [IsSimpleGroup X] [Group G]
    (hX : ¬ Group.IsSolvable X) (f : X →* G) (hf : Function.Injective f) :
    NoSolvableRadical f.range := by
  rw [MonoidHom.range_eq_map]
  exact noSolvableRadical_map f hf (noSolvableRadical_top hX)

end CFSG.RankThree.PartOne.KLR
