module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.StandardType.ClassicalBlocks

open Matrix

@[expose] def GUFull (m Q : ℕ) (E : Type) [Field E] : Subgroup (GL (Fin m) E) :=
  Subgroup.closure {A : GL (Fin m) E |
    ((A : Matrix (Fin m) (Fin m) E).map (· ^ Q))ᵀ * (A : Matrix (Fin m) (Fin m) E) = 1}

@[expose] noncomputable def eigDim {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : Matrix ι ι K) (l : AlgebraicClosure K) : ℕ :=
  Module.finrank (AlgebraicClosure K)
    (Module.End.eigenspace (Matrix.toLin' (b.map (algebraMap K (AlgebraicClosure K)))) l)

@[expose] noncomputable def eigDimOn {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b e : Matrix ι ι K) (l : AlgebraicClosure K) : ℕ :=
  Module.finrank (AlgebraicClosure K)
    ↥(Module.End.eigenspace (Matrix.toLin' (b.map (algebraMap K (AlgebraicClosure K)))) l ⊓
      LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K)))))

@[expose] noncomputable def blockExp {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (orth : Bool) (b : Matrix ι ι K) : ℕ :=
  haveI := Classical.decEq (AlgebraicClosure K)
  (if orth then (eigDim b 1 / 2) * (eigDim b 1 / 2 - 1) else (eigDim b 1 / 2) ^ 2) +
    (∑ l ∈ ((b.charpoly.map (algebraMap K (AlgebraicClosure K))).roots.toFinset).erase 1,
      eigDim b l * (eigDim b l - 1) / 2) / 2

end CFSG.StandardType.ClassicalBlocks
