module

public import CFSG.Permutation.FiveTransitive.MovingStabilizer
public import CFSG.Permutation.FiveTransitive.TwoPairTransitivity
public import CFSG.Permutation.FiveTransitive.OyamaTripleOrbits
public import CFSG.Permutation.FiveTransitive.OyamaThreeOrbitOrders

public section

namespace CFSG

namespace FiveTransitive.OyamaOrbitDichotomy

open MulAction SubMulAction

variable {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]

private theorem four_transitive_of_one_orbit
    (hcond : OyamaConditionStar.Condition G X) (e : Fin 3 ↪ X)
    (hone : Nat.card (orbitRel.Quotient (fixingSubgroup G (Set.range e))
      (ofFixingSubgroup G (Set.range e))) = 1) : IsMultiplyPretransitive G X 4 := by
  classical
  let b : Fin 2 ↪ X := (Fin.castAddEmb 1).trans e
  let a := e 2
  have ha : a ∉ Set.range b := by
    rintro ⟨i,hi⟩
    fin_cases i
    · exact e.injective.ne (by decide : (0 : Fin 3) ≠ 2) hi
    · exact e.injective.ne (by decide : (1 : Fin 3) ≠ 2) hi
  have hset : insert a (Set.range b) = Set.range e := by
    ext x
    constructor
    · rintro (h | ⟨i,hi⟩)
      · exact ⟨2,h.symm⟩
      · exact ⟨Fin.castAdd 1 i,hi⟩
    · rintro ⟨i,rfl⟩
      fin_cases i
      · exact Set.mem_insert_of_mem a ⟨0,rfl⟩
      · exact Set.mem_insert_of_mem a ⟨1,rfl⟩
      · exact Set.mem_insert a _
  have htrans : IsPretransitive (fixingSubgroup G (Set.range e))
      (ofFixingSubgroup G (Set.range e)) := by
    let _ : Subsingleton (orbitRel.Quotient (fixingSubgroup G (Set.range e))
      (ofFixingSubgroup G (Set.range e))) := Finite.card_le_one_iff_subsingleton.mp (by omega)
    constructor
    intro x y
    exact mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact
      (Subsingleton.elim (Quotient.mk'' y) (Quotient.mk'' x))))
  obtain ⟨Q,hQ,hfix⟩ := OyamaConditionPair.exists_pair_fixed_subgroup hcond (b 0) (b 1)
    (b.injective.ne (by decide))
  have hrange : Set.range b = {b 0,b 1} := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · exact ⟨0,hx.symm⟩
      · exact ⟨1,(Set.mem_singleton_iff.mp hx).symm⟩
  have han : a ∉ fixedPoints Q X := by rwa [hfix,←hrange]
  have hmove : ∃ g : fixingSubgroup G (Set.range b), (g : G) • a ≠ a := by
    have hex : ∃ q : Q, q • a ≠ a := by
      by_contra! hn
      exact han (mem_fixedPoints.mpr hn)
    obtain ⟨q,hq⟩ := hex
    have hm : q.val ∈ fixingSubgroup G (Set.range b) := by
      rw [mem_fixingSubgroup_iff]
      intro x hx
      have hxQ : x ∈ fixedPoints Q X := by rwa [hfix,←hrange]
      exact mem_fixedPoints.mp hxQ q
    exact ⟨⟨q.val,hm⟩,hq⟩
  have hpair := MovingStabilizer.fixer_complement_two_transitive (Set.range b) a ha hmove
    (by rw [hset]; exact htrans)
  exact TwoPairTransitivity.four_transitive (OyamaConditionPair.two_transitive hcond) b hpair

theorem four_transitive_or_three_orbits
    (hcond : OyamaConditionStar.Condition G X) :
    IsMultiplyPretransitive G X 4 ∨ OyamaThreeOrbitOrders.ThreeOrbits G X := by
  classical
  by_cases h4 : IsMultiplyPretransitive G X 4
  · exact Or.inl h4
  right
  intro s hs
  have heven : Even (Nat.card X) := Nat.even_iff.mpr
    (EvenSixDegreeBound.degree_mod_two (by have := hcond.1; omega) hcond.2.1)
  have hfour : OyamaTripleSylow.FourFixedSix G X := by
    intro t ht T
    exact (EvenSixTupleLocal.to_set_property hcond.2.1 t ht T).1
  rcases OyamaTripleOrbits.card_orbits_eq_one_or_three heven hfour s hs with hone | hthree
  · have hc : Nat.card s = 3 := by rwa [Nat.card_coe_set_eq]
    let f : s ≃ Fin 3 := Finite.equivFinOfCardEq hc
    let e : Fin 3 ↪ X := f.symm.toEmbedding.trans (Function.Embedding.subtype _)
    have he : Set.range e = s := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩
        exact (f.symm i).property
      · intro hx
        exact ⟨f ⟨x,hx⟩,congrArg Subtype.val (f.symm_apply_apply ⟨x,hx⟩)⟩
    exact (h4 (four_transitive_of_one_orbit hcond e (by rwa [he]))).elim
  · exact hthree

end FiveTransitive.OyamaOrbitDichotomy

end CFSG
