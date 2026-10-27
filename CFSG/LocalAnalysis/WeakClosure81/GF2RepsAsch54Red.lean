module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Rad

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.Quasithin.Vol2.Ch11.SecB (E111Reduced)
open CFSG.Quasithin.E2.E22N.E111R (IsComp)

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem normalClosure_component_le_layer {E : Subgroup Y} (hE : CFSG.IsComponent E) :
    Subgroup.normalClosure (E : Set Y) ≤ CFSG.layer Y := by
  have : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
  exact normalClosure_le_normal (CFSG.LocalCores.component_le_layer hE)

theorem isComp_normalClosure (hrad : CFSG.solvableRadical Y = ⊥) {E : Subgroup Y}
    (hE : CFSG.IsComponent E) : IsComp (Subgroup.normalClosure (E : Set Y)) E :=
  ⟨le_normalClosure, normal_subgroupOf_of_le_normalizer
    ((normalClosure_component_le_layer hE).trans (CFSG.LocalCores.layer_le_normalizer hE)),
    isSimpleGroup_of_isComponent hrad hE⟩

theorem normalClosure_component_minimal (hrad : CFSG.solvableRadical Y = ⊥) {E : Subgroup Y}
    (hE : CFSG.IsComponent E) (N : Subgroup Y) (hN : N.Normal)
    (hNX : N ≤ Subgroup.normalClosure (E : Set Y)) :
    N = ⊥ ∨ N = Subgroup.normalClosure (E : Set Y) := by
  rcases CFSG.LocalCores.component_normal_subgroup hE hN with h | h
  · exact Or.inr (le_antisymm hNX (normalClosure_le_normal h))
  · left
    have hC : Subgroup.normalClosure (E : Set Y) ≤ centralizer (N : Set Y) :=
      normalClosure_le_normal (commutator_eq_bot_iff_le_centralizer.mp h)
    have hs : Group.IsSolvable ↥N := Group.isSolvable_of_comm fun a b =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hC (hNX b.2)) a a.2)
    rw [eq_bot_iff, ← hrad]
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical hN hs

omit [Finite Y] in
theorem centralizer_eq_bot_of_sup_eq_top (hrad : CFSG.solvableRadical Y = ⊥) {X S : Subgroup Y}
    [X.Normal] [Group.IsSolvable ↥S] (hXS : X ⊔ S = ⊤) : centralizer (X : Set Y) = ⊥ := by
  have : Group.IsSolvable (Y ⧸ X) := by
    refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' X).comp S.subtype) fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective X q
    have hy : y ∈ X ⊔ S := by
      rw [hXS]
      exact mem_top y
    obtain ⟨x, hx, s, hs, rfl⟩ := mem_sup_of_normal_left.mp hy
    refine ⟨⟨s, hs⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff x).mpr hx, one_mul]
  set C := centralizer (X : Set Y)
  let g : ↥C →* Y ⧸ X := (QuotientGroup.mk' X).comp C.subtype
  have : Group.IsSolvable ↥g.ker := Group.isSolvable_of_comm fun a b => by
    have hb : ((b : ↥C) : Y) ∈ X :=
      (QuotientGroup.eq_one_iff ((b : ↥C) : Y)).mp (MonoidHom.mem_ker.mp b.2)
    exact Subtype.ext (Subtype.ext (Subgroup.mem_centralizer_iff.mp (a : ↥C).2 _ hb).symm)
  have hCs : Group.IsSolvable ↥C :=
    Group.isSolvable_of_ker_le_range g.ker.subtype g (Subgroup.range_subtype g.ker).ge
  rw [eq_bot_iff, ← hrad]
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical inferInstance hCs

theorem e111Reduced_normalClosure (hrad : CFSG.solvableRadical Y = ⊥) {E S : Subgroup Y}
    (hE : CFSG.IsComponent E) (hS : IsSylowIn 2 S ⊤) (hES : E ⊔ S = ⊤) :
    E111Reduced Y (Subgroup.normalClosure (E : Set Y)) S ∧
      IsComp (Subgroup.normalClosure (E : Set Y)) E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := isComp_normalClosure hrad hE
  have hXS : Subgroup.normalClosure (E : Set Y) ⊔ S = ⊤ := by
    rw [eq_top_iff, ← hES]
    exact sup_le_sup_right le_normalClosure S
  have : Group.IsSolvable ↥S := by
    have := hS.isPGroup.isNilpotent
    infer_instance
  obtain ⟨a, b, hab⟩ := hc.nonabelian
  exact ⟨⟨normalClosure_normal, fun h => hc.ne_bot (le_bot_iff.mp (le_normalClosure.trans h.le)),
    normalClosure_component_minimal hrad hE,
    ⟨⟨a, le_normalClosure a.2⟩, ⟨b, le_normalClosure b.2⟩,
      fun h => hab (Subtype.ext (by simpa using congrArg Subtype.val h))⟩,
    centralizer_eq_bot_of_sup_eq_top hrad hXS, hS, hXS⟩, hc⟩

end CFSG.LocalAnalysis.WeakClosure81

end
