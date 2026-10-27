module

public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalD4

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCOrthogonal

section Defs

variable {K : Type} [Field K] {d : ℕ}

abbrev matrixFixedSpace (x : GL (Fin d) K) : Submodule K (Fin d → K) :=
  fixedSpace (matrixLinearEquiv x)

@[expose] def IsSplitFourSpace {W : Type*} [AddCommGroup W] [Module K W] (Q : QuadraticForm K W) :
    Prop :=
  finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ s ∈ S, Q s = 0

@[expose] def supportedMatrix (Q : QuadraticForm K (Fin d → K)) (W : Submodule K (Fin d → K)) :
    Subgroup (GL (Fin d) K) :=
  (supportedOrthDerived Q W).comap matrixLinearIso.toMonoidHom

@[expose] noncomputable def supportedInner (Q : QuadraticForm K (Fin d → K))
    (W : Submodule K (Fin d → K)) : Subgroup (MulAut (matrixProjectiveDerived Q)) :=
  ((supportedMatrix Q W).subgroupOf (matrixDerived Q)).map
    ((MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).comp
      (matrixProjectiveProjection Q))

theorem mem_supportedInner {Q : QuadraticForm K (Fin d → K)} {W : Submodule K (Fin d → K)}
    {c : MulAut (matrixProjectiveDerived Q)} :
    c ∈ supportedInner Q W ↔ ∃ g : matrixDerived Q, g.val ∈ supportedMatrix Q W ∧
      MulAut.conj (matrixProjectiveProjection Q g) = c := by
  simp only [supportedInner, Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]

end Defs

section Odd

variable {K : Type} [Field K] {d : ℕ}

@[expose] def OddD4Witness (Q : QuadraticForm K (Fin d → K))
    (a : MulAut (matrixProjectiveDerived Q)) (W : Submodule K (Fin d → K)) : Prop :=
  supportedMatrix Q W ≤ matrixDerived Q ∧
  (∀ D : Subgroup (MulAut (matrixProjectiveDerived Q)),
    CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ D →
      supportedInner Q W ≤ layerCentralizer D a) ∧
  (∃ u ∈ W, ∃ v ∈ W, Q u = 1 ∧ Q v = 1 ∧ polar Q u v = 0) ∧
  (∀ u ∈ W, ∀ v ∈ W, Q u = 1 → Q v = 1 → polar Q u v = 0 →
    ∃ g : matrixDerived Q, matrixLinearEquiv g.val = reflect Q u * reflect Q v ∧
      g.val ∈ supportedMatrix Q W ∧
      orderOf (MulAut.conj (matrixProjectiveProjection Q g)) = 2 ∧
      MulAut.conj (matrixProjectiveProjection Q g) ∈ supportedInner Q W ∧
      Subgroup.centralizer
        ({MulAut.conj (matrixProjectiveProjection Q g)} : Set (MulAut (matrixProjectiveDerived Q)))
        ≤ matrixProjectiveImage Q) ∧
  Subgroup.centralizer (supportedInner Q W : Set (MulAut (matrixProjectiveDerived Q))) ≤
    matrixProjectiveImage Q ∧
  ∀ D : Subgroup (MulAut (matrixProjectiveDerived Q)),
    CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ D →
      Subgroup.centralizer (layerCentralizer D a : Set (MulAut (matrixProjectiveDerived Q))) ≤
        matrixProjectiveImage Q

end Odd

end CFSG.RankThree.PartOne.KCOrthogonalD4
