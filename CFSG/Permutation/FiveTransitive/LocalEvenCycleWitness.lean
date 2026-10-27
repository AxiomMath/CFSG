module

public import CFSG.Permutation.FiveTransitive.PatternFixerNormalizer
public import CFSG.Permutation.FiveTransitive.FixedSetCycleRoots
public import CFSG.Permutation.FiveTransitive.SixPointCycleCounts
public import CFSG.Permutation.FiveTransitive.SixLocalSylowExponentTwo
public import CFSG.Permutation.FiveTransitive.CyclePatternFinite

public section

namespace CFSG

namespace FiveTransitive.LocalEvenCycleWitness

open MulAction Equiv FixedSetNormalizerPerm CyclePatternRoots FixedSetCycleRoots

variable {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]

omit [Fintype X] in
theorem exists_normalizer
    (a : G) (k : ℕ) (ha : orderOf a = 2 ^ k)
    (e : Fin 4 ↪ X) (π : Perm (Fin 4)) (he : ∀ i, a • e i = e (π i)) :
    ∃ S : Sylow 2 (fixingSubgroup G (Set.range e)),
      let Q := (S : Subgroup (fixingSubgroup G (Set.range e))).map
        (fixingSubgroup G (Set.range e)).subtype
      a ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ i, e i ∈ fixedPoints Q X := by
  obtain ⟨S,hS⟩ := NormalizerInvariantSylow.exists_of_order_pow 2 G
    (fixingSubgroup G (Set.range e)) a (PatternFixerNormalizer.normalizes_range a e π he) k ha
  refine ⟨S,hS,?_⟩
  intro i
  rw [mem_fixedPoints]
  intro q
  obtain ⟨r,hr,hqr⟩ := Subgroup.mem_map.mp q.property
  change (q : G) • e i = e i
  rw [←hqr]
  exact (mem_fixingSubgroup_iff G).mp r.property (e i) ⟨i,rfl⟩

theorem two_le_of_four_root
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (a : G) (k : ℕ) (ha : orderOf a = 2 ^ k)
    (hfour : 0 < Nat.card (FourRoot (toPermHom G X a))) :
    2 ≤ Nat.card (TwoRoot (toPermHom G X a)) := by
  classical
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp hfour).1
  let E := (CyclePatternRoots.fourEquiv (toPermHom G X a)).symm x
  obtain ⟨S,hS,hfix⟩ := exists_normalizer a k ha E.val (finRotate 4) E.property
  let Q := (S : Subgroup (fixingSubgroup G (Set.range E.val))).map
    (fixingSubgroup G (Set.range E.val)).subtype
  obtain ⟨hc,he⟩ := hlocal (Set.range E.val)
    (by simpa only [Nat.card_fin] using Set.ncard_range_of_injective E.val.injective) S
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  let f := fixedPerm G X Q a hS
  let ef := liftTuple Q E.val hfix
  have hfpat : ∀ i, f (ef i) = ef (finRotate 4 i) := by
    intro i
    apply Subtype.ext
    exact E.property i
  let r : FourRoot f := CyclePatternRoots.fourEquiv f ⟨ef,hfpat⟩
  have hfpos : 0 < Nat.card (FourRoot f) := Nat.card_pos_iff.mpr ⟨⟨r⟩,inferInstance⟩
  have hcount := (SixPointCycleCounts.counts
    (by simpa only [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hc) f (he a hS)).1 hfpos
  rw [←hcount]
  exact Nat.card_le_card_of_injective (twoEmbedding Q a hS) (twoEmbedding Q a hS).injective

theorem two_le_fixed_of_double_two
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (a : G) (k : ℕ) (ha : orderOf a = 2 ^ k)
    (E : Pattern (toPermHom G X a) CyclePatternFinite.doubleTwo) :
    2 ≤ Nat.card (Function.fixedPoints (toPermHom G X a)) := by
  classical
  obtain ⟨S,hS,hfix⟩ := exists_normalizer a k ha E.val CyclePatternFinite.doubleTwo E.property
  let Q := (S : Subgroup (fixingSubgroup G (Set.range E.val))).map
    (fixingSubgroup G (Set.range E.val)).subtype
  obtain ⟨hc,he⟩ := hlocal (Set.range E.val)
    (by simpa only [Nat.card_fin] using Set.ncard_range_of_injective E.val.injective) S
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  let f := fixedPerm G X Q a hS
  let ef := liftTuple Q E.val hfix
  have hfpat : ∀ i, f (ef i) = ef (CyclePatternFinite.doubleTwo i) := by
    intro i
    apply Subtype.ext
    exact E.property i
  have hsq (i : Fin 4) : CyclePatternFinite.doubleTwo (CyclePatternFinite.doubleTwo i) = i := by
    revert i
    decide
  have hne (i : Fin 4) : CyclePatternFinite.doubleTwo i ≠ i := by
    revert i
    decide
  let er : Fin 4 ↪ TwoRoot f :=
    ⟨fun i => ⟨ef i,by
      constructor
      · rw [hfpat,hfpat,hsq]
      · intro h
        rw [hfpat] at h
        exact hne i (ef.injective h)⟩,
      fun i j h => ef.injective (congrArg Subtype.val h)⟩
  have hfour : 4 ≤ Nat.card (TwoRoot f) := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective er er.injective
  have htwo := (SixPointCycleCounts.counts
    (by simpa only [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hc) f (he a hS)).2 hfour
  exact htwo.trans (Nat.card_le_card_of_injective
    (fixedEmbedding Q a hS) (fixedEmbedding Q a hS).injective)

end FiveTransitive.LocalEvenCycleWitness

end CFSG
