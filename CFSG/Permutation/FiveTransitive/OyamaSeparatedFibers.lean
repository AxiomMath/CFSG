module

public import CFSG.Permutation.FiveTransitive.SeparatedEightTupleFibers
public import CFSG.Permutation.FiveTransitive.OyamaSixPointOrbits
public import CFSG.Permutation.FiveTransitive.OyamaDoubleSwapWitness

public section

namespace CFSG

namespace FiveTransitive.OyamaSeparatedFibers

open MulAction OyamaFourFiberGeometry

variable (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]

private theorem exists_fibers
    (h4 : IsMultiplyPretransitive G X 4) (b : Fin 4 ↪ X)
    (S : Sylow 2 (fixingSubgroup G (Set.range b)))
    (hH : fixedPoints (fixingSubgroup G (Set.range b)) X = Set.range b)
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G (Set.range b))).map (fixingSubgroup G (Set.range b)).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hS : Nat.card S = 16) :
    ∃ e : Fin 3 → Fiber (G := G) b,
      ∀ i j : Fin 3, i ≠ j → ∀ c d : Bool,
        ¬ orbitRel (stabilizer G b) X (cycleTuple b (e i) (if c then 1 else 0))
          (cycleTuple b (e j) (if d then 1 else 0)) := by
  have hs : (Set.range b).ncard = 4 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have hn := (OyamaSixOddOrbits.degree_and_odd_orbits G X h4 (Set.range b) hs S hfree hcard himage hS).1
  have hn10 : 10 ≤ Fintype.card X := by rw [Nat.card_eq_fintype_card] at hn; omega
  let _ : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u,v,w,hu,hv,_,hF,hvu,_,_,_,huc,hvc,hw⟩ :=
    OyamaSixPointOrbits.exists_geometry G X h4 (Set.range b) hs S hH hfree hcard himage hS
  obtain ⟨a,ha,hbase,hsquare,hfix⟩ :=
    OyamaDoubleSwapWitness.exists_witness G X hn10 h4 b S hfree hcard himage hS
  rw [EvenSixTupleLocal.fixing_range] at hvu huc hvc hw
  exact SeparatedEightTupleFibers.exists_fibers b (fixedPoints S X) u v w hF hu hv hvu huc hvc hw
    a ha hbase hfix hsquare

theorem six_le_orbits
    (h4 : IsMultiplyPretransitive G X 4) (b : Fin 4 ↪ X)
    (S : Sylow 2 (fixingSubgroup G (Set.range b)))
    (hH : fixedPoints (fixingSubgroup G (Set.range b)) X = Set.range b)
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G (Set.range b))).map (fixingSubgroup G (Set.range b)).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hS : Nat.card S = 16) :
    6 ≤ Nat.card (orbitRel.Quotient (stabilizer G b) (Fiber (G := G) b)) := by
  have hs : (Set.range b).ncard = 4 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have hsq := (OyamaSixElementary.square_eq_one_and_commute G X h4 (Set.range b) hs
    S hfree hcard himage).1
  have ht : ∃ T : Sylow 2 (stabilizer G b), ∀ q : T, q * q = 1 := by
    rw [← EvenSixTupleLocal.fixing_range]
    exact ⟨S,hsq⟩
  obtain ⟨T,hT⟩ := ht
  obtain ⟨e,hsep⟩ := exists_fibers G X h4 b S hH hfree hcard himage hS
  exact OyamaFourFiberGeometry.six_le_orbits b T hT e hsep

end FiveTransitive.OyamaSeparatedFibers

end CFSG
