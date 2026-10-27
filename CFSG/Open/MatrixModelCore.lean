module

public import Mathlib
public meta import Lean.Elab.Term
public meta import Lean.Meta.Tactic.Delta

public section

open Lean Elab Term Meta in
elab "matrix_model% " t:term : term <= ty => do
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let e ← deltaExpand e (fun n => n == `CFSG.MatrixModel.unitaryCore ||
    n == `CFSG.MatrixModel.slCore || n == `CFSG.MatrixModel.isometryCore ||
    n == `CFSG.MatrixModel.gramCore ||
    n == `CFSG.MatrixModel.plusQuadCore || n == `CFSG.MatrixModel.minusQuadCore)
  Core.betaReduce e

namespace CFSG.MatrixModel

open Matrix

@[expose] def unitaryCore (ι : Type*) [Fintype ι] [DecidableEq ι] (K : Type*) [Field K] (q : ℕ) :
    Subgroup (GL ι K) :=
  Subgroup.closure {A | (A : Matrix ι ι K).det = 1 ∧
    ((A : Matrix ι ι K).map (· ^ q))ᵀ * (A : Matrix ι ι K) = 1}

@[expose] def slCore (ι : Type*) [Fintype ι] [DecidableEq ι] (K : Type*) [Field K] :
    Subgroup (GL ι K) :=
  (GeneralLinearGroup.det : GL ι K →* Kˣ).ker

@[expose] def isometryCore {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : (ι → K) → K) : Subgroup (GL ι K) :=
  Subgroup.closure {A : GL ι K | ∀ v : ι → K, Q (Matrix.mulVec (A : Matrix ι ι K) v) = Q v}

@[expose] def gramCore {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] (J : Matrix ι ι K) :
    Subgroup (GL ι K) :=
  Subgroup.closure {A |
    @HMul.hMul (Matrix ι ι K) (Matrix ι ι K) (Matrix ι ι K) instHMul (A : Matrix ι ι K)ᵀ J *
      (A : Matrix ι ι K) = J}

@[expose] def plusQuadCore (m : ℕ) (K : Type*) [Field K] (v : Fin m ⊕ Fin m → K) : K :=
  ∑ i : Fin m, v (Sum.inl i) * v (Sum.inr i)

@[expose] def minusQuadCore (m : ℕ) (K : Type*) [Field K] (b c : K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) : K :=
  ∑ i : Fin m, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
    b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c * v (Sum.inr (Sum.inr 1)) ^ 2

end CFSG.MatrixModel
