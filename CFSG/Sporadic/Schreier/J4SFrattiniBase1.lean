
module

public import CFSG.Sporadic.Schreier.J4SFrattiniBase
import all CFSG.Sporadic.Schreier.J4SFrattiniBase

public import CFSG.Sporadic.Schreier.J4SSylowNodeBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem exists_etaV {n : J} (hn : n ∈ N) : ∃ a, etaV a = n := by
  obtain ⟨i, -, rfl⟩ := exists_η_eq hn
  exact ⟨toVecD 11 i, etaV_toVecD i⟩

theorem ellV_colsMatrix
    {e : ℕ} (he : e < 1024) (a : Fin 11 → ZMod 2) :
    ellV (colsMatrix elementColumns[e]! *ᵥ a) = ellV a := by
  rw [ellV, Matrix.dotProduct_mulVec, ell_vecMul e he, ellV]

theorem etaV_zero : etaV 0 = 1 := by
  rw [etaV_eq, ofAdd_zero, map_one]

end CFSG.Sporadic.J4Schreier
