module

public import CFSG.Permutation.FiveTransitive.OyamaSeparatedFibers
public import CFSG.Permutation.FiveTransitive.OyamaSixCycleShape
public import CFSG.Permutation.FiveTransitive.OyamaOrderEightOccurrences
public import CFSG.Permutation.FiveTransitive.OyamaFourBaseOrbitCount

public section

namespace CFSG

namespace FiveTransitive.OyamaSixteenContradiction

open MulAction OyamaFourFiberGeometry

theorem contradiction
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (b : Fin 4 ↪ X)
    (S : Sylow 2 (fixingSubgroup G (Set.range b)))
    (hH : fixedPoints (fixingSubgroup G (Set.range b)) X = Set.range b)
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G (Set.range b))).map (fixingSubgroup G (Set.range b)).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hS : Nat.card S = 16) : False := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hs : (Set.range b).ncard = 4 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have hn := (OyamaSixOddOrbits.degree_and_odd_orbits G X h4 (Set.range b) hs S hfree hcard himage hS).1
  have hn10 : 10 ≤ Fintype.card X := by rw [Nat.card_eq_fintype_card] at hn; omega
  have hshape := OyamaSixCycleShape.shape G X h4 (Set.range b) hs S hfree hcard himage
  obtain ⟨htwo,hfour⟩ := OyamaOrderEightOccurrences.two_and_four_occur
    G X hn10 h4 (Set.range b) hs S hfree hcard himage hS
  have hlo := OyamaSeparatedFibers.six_le_orbits G X h4 b S hH hfree hcard himage hS
  have hhi := OyamaFourBaseOrbitCount.four_orbits G X h4 (by omega)
    hshape htwo hfour basePositions b
  change Nat.card (orbitRel.Quotient (stabilizer G b) (Fiber (G := G) b)) = 4 at hhi
  omega

end FiveTransitive.OyamaSixteenContradiction

end CFSG
