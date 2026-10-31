module

public import CFSG.Permutation.FiveTransitive.SeparatedTupleOrbits
public import CFSG.Permutation.FiveTransitive.CyclePatternFinite
public import CFSG.Permutation.FiveTransitive.FrobeniusCyclePattern
public import CFSG.Permutation.FiveTransitive.TupleFiberOrbits

public section

namespace CFSG

namespace FiveTransitive.OyamaFourFiberGeometry

open MulAction Equiv

@[expose] def basePositions : Fin 4 ↪ Fin 8 := Fin.natAddEmb 4
@[expose] def cyclePositions : Fin 4 ↪ Fin 8 := Fin.castAddEmb 4

private def turn : Perm (Fin 8) := CyclePatternFinite.transport finSumFinEquiv
  ((finRotate 4).sumCongr (1 : Perm (Fin 4)))

private theorem turn_base (i : Fin 4) : turn (basePositions i) = basePositions i := by
  revert i
  decide

private theorem turn_cycle (i : Fin 4) : turn (cyclePositions i) =
    cyclePositions (finRotate 4 i) := by
  revert i
  decide

private theorem turn_commutes (i : Fin 8) :
    CyclePatternFinite.fourTwoTwo (turn i) = turn (CyclePatternFinite.fourTwoTwo i) := by
  revert i
  decide

variable {G X : Type*} [Group G] [MulAction G X]

abbrev Admissible := FrobeniusCyclePattern.admissible (G := G) (X := X)
  CyclePatternFinite.fourTwoTwo

abbrev Fiber (b : Fin 4 ↪ X) := TupleFiberOrbits.fiber
  (Admissible (G := G) (X := X)) basePositions b

private def rotateFiber (b : Fin 4 ↪ X) (e : Fiber (G := G) b) : Fiber (G := G) b := by
  let v : Fin 8 ↪ X := turn.toEmbedding.trans e.val.val
  have hv : v ∈ Admissible (G := G) (X := X) := by
    apply (FrobeniusCyclePattern.mem_admissible_iff _ _).mpr
    obtain ⟨g,hg⟩ := (FrobeniusCyclePattern.mem_admissible_iff _ _).mp e.val.property
    refine ⟨g,?_⟩
    intro i
    change g • e.val.val (turn i) = e.val.val (turn (CyclePatternFinite.fourTwoTwo i))
    rw [hg,turn_commutes]
  refine ⟨⟨v,hv⟩,?_⟩
  apply Function.Embedding.ext
  intro i
  change e.val.val (turn (basePositions i)) = b i
  rw [turn_base]
  exact DFunLike.congr_fun e.property i

@[expose] def cycleTuple (b : Fin 4 ↪ X) (e : Fiber (G := G) b) : Fin 4 ↪ X :=
  cyclePositions.trans e.val.val

private theorem cycleTuple_smul (b : Fin 4 ↪ X) (g : stabilizer G b) (e : Fiber (G := G) b) :
    cycleTuple b (g • e) = g • cycleTuple b e := rfl

private theorem cycleTuple_rotate (b : Fin 4 ↪ X) (e : Fiber (G := G) b) :
    cycleTuple b (rotateFiber b e) = SeparatedTupleOrbits.rotate (cycleTuple b e) := by
  apply Function.Embedding.ext
  intro i
  change e.val.val (turn (cyclePositions i)) = e.val.val (cyclePositions (finRotate 4 i))
  rw [turn_cycle]

theorem six_le_orbits [Finite G] [Finite X]
    (b : Fin 4 ↪ X) (S : Sylow 2 (stabilizer G b)) (hS : ∀ q : S, q * q = 1)
    (e : Fin 3 → Fiber (G := G) b)
    (hsep : ∀ i j : Fin 3, i ≠ j → ∀ c d : Bool,
      ¬ orbitRel (stabilizer G b) X (cycleTuple b (e i) (if c then 1 else 0))
        (cycleTuple b (e j) (if d then 1 else 0))) :
    6 ≤ Nat.card (orbitRel.Quotient (stabilizer G b) (Fiber (G := G) b)) := by
  simpa only [Fintype.card_fin] using
    SeparatedTupleOrbits.projected_twice_card_le S hS (cycleTuple b) (cycleTuple_smul b)
      (rotateFiber b) (cycleTuple_rotate b) e hsep

end FiveTransitive.OyamaFourFiberGeometry

end CFSG
