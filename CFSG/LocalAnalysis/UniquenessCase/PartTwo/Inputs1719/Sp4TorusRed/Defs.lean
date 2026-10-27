module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRoots
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherInvariant

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def IsRootFree (X : Subgroup (StatedSp 2 K)) : Prop :=
  ∀ (a b : Fin 2 ⊕ Fin 2) (hab : a ≠ b) (t : K), pairRootElt hab t ∈ X → t = 0

@[expose] def IsTorusReducible (H : Subgroup (StatedSp 2 K)) : Prop :=
  ∃ W : Submodule K (Fin 2 ⊕ Fin 2 → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
    (∀ d ∈ torus 2 K, ∀ w ∈ W,
      ((d : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ w ∈ W) ∧
    ∀ h ∈ H, ∀ w ∈ W,
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ w ∈ W

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
