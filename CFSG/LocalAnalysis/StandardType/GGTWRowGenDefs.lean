module

public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBTorAFrom (r₀ : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .A ∨ lab.tag = .twA) → r₀ ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      ¬ (p = 3 ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n + 1) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
          (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I

@[expose] def GGTBTorLiftAFrom (r₀ : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .A ∨ lab.tag = .twA) → r₀ ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      ¬ (p = 3 ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n + 1) →
      LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - 1 - ggTorEnn p lab) R

@[expose] def GGTWRowPred (r₀ p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∨ lab.tag = .twA) ∧ r₀ ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab ∧
    ¬ (p = 3 ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n + 1)

end CFSG.StandardType

end
