module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.Chevalley.GraphFixedF4Intertwiner

public section

namespace CFSG.StandardType.E6GraphNoneSteps

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6

@[expose] def movedPos : List (Fin 6 → ℤ) :=
  [![0,0,0,0,0,1], ![0,0,0,0,1,0], ![0,0,0,0,1,1], ![0,0,0,1,1,0], ![0,0,0,1,1,1],
   ![0,0,1,0,0,0], ![0,0,1,1,0,0], ![0,0,1,1,1,1], ![0,1,0,1,1,0], ![0,1,0,1,1,1],
   ![0,1,1,1,0,0], ![0,1,1,1,1,1], ![0,1,1,2,1,1], ![0,1,1,2,2,1], ![1,0,0,0,0,0],
   ![1,0,1,0,0,0], ![1,0,1,1,0,0], ![1,0,1,1,1,0], ![1,1,1,1,0,0], ![1,1,1,1,1,0],
   ![1,1,1,2,1,0], ![1,1,1,2,2,1], ![1,1,2,2,1,0], ![1,1,2,2,1,1]]

@[expose] def e6R (m : Fin 72) : Fin 6 → ℤ := fun i => e6RootVec m i

@[expose] def rhoV (v : Fin 6 → ℤ) : Fin 6 → ℤ := ![v 5, v 1, v 4, v 3, v 2, v 0]

theorem rhoV_eq (v : Fin Tag.E6.rank → ℤ) : rhoV v = permLattice TwistTag.E6.perm v := by
  funext j
  fin_cases j <;> rfl

theorem movedPos_spec : ∀ α ∈ movedPos, (∃ m : Fin 72, e6R m = α) ∧
    (∃ m : Fin 72, e6R m = rhoV α) ∧ rhoV α ≠ α ∧
    (∀ m : Fin 72, e6R m ≠ α + rhoV α) ∧ (∀ m : Fin 72, e6R m ≠ α + -rhoV α) ∧
    0 < ∑ i, α i ∧ 0 < ∑ i, rhoV α i := by
  decide +kernel

end CFSG.StandardType.E6GraphNoneSteps
