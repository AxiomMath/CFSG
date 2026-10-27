module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4ComponentIdent
public import CFSG.LocalAnalysis.StandardType.GGInnerD4Regimes
public import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType.S2MathAs51600DGenSelected

open CFSG CFSG.Assembly
open CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.KCOrthogonal

@[expose] def DGenSelectedMarking : Prop :=
  ∀ (X : Type*) [Group X] [Finite X] (A : Subgroup (MulAut X)),
    CFSG.StandardType.LargeEvenMarking X
      (fun lab _ _ I _ θ =>
        ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∧
          GGInducedInn A θ I) →
    CFSG.StandardType.LargeEvenMarking X
      (fun lab R _ I _ θ =>
        (((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∧
          GGInducedInn A θ I) ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
          (V : Type) (_ : AddCommGroup V) (_ : Module K V)
          (_ : FiniteDimensional K V)
          (Q : QuadraticForm K V)
          (e : R ≃* ProjOrthDerived Q),
          Nat.card K = 2 ^ lab.n ∧
          (QuadraticMap.polarBilin Q).Nondegenerate ∧
          (∃ U : Submodule K V, Module.finrank K U = 3 ∧
            ∀ u ∈ U, Q u = 0) ∧
          GGInducedInn A (θ.trans e)
            (LargeEvenInnSet (ProjOrthDerived Q)) ∧
          ∀ σ : MulAut X,
            ggInducedAut (θ.trans e) σ =
              MulAut.congr e (ggInducedAut θ σ))

end CFSG.StandardType.S2MathAs51600DGenSelected
