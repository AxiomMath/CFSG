
module

public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.ON.Certificate
public import CFSG.F3.ConjSpec

public section

namespace CFSG.Sporadic.ON

open Native Matrix
open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (lettersOf instrLt ordOK inTreeB labelsOf)

noncomputable abbrev orb : VOrbit := orbitData ()

noncomputable abbrev posF : W → ℕ := fun x => (Native.indexOf orb.keys).getD x nPts

noncomputable abbrev negT : Table := negTable orb posF

noncomputable abbrev basisR : Array W := basisRows orb

noncomputable abbrev basisX : Array W := invW 154 basisR

noncomputable abbrev regsT : Array Table := regs0 orb

noncomputable abbrev slp : Array Table × Bool := runSLP nPts prog regsT

noncomputable abbrev letters : Array Table := lettersOf nPts sel slp.1

noncomputable abbrev trees : Array Tree := chainTrees nPts letters chainBase

noncomputable abbrev reps : Table := lineReps negT

noncomputable abbrev lineT : Table := lineOfT negT reps

noncomputable abbrev lineL : Array Table := lineLetters letters reps lineT

noncomputable abbrev lv1 : Array ℕ := levelLetters letters chainBase 1

noncomputable abbrev subT : Array Tree := subTreesOf lineL lv1

noncomputable abbrev labs : Array ℕ := labelsOf nLines subT

structure Facts : Prop where
  matrix : matrixChecks = true
  orbit : Native.orbitOK nPts colsA colsB orb posF 3 = true
  neg : negOK nPts orb negT = true
  basis : basisChecks basisR basisX = true
  chain : chainChecks orb negT slp.2 letters trees 3 = true
  lines : lineChecks negT reps lineT = true
  sub : subChecks lineL lv1 subT labs = true
  support : supportChecks orb basisR basisX = true
  ord : ordChecks regsT = true

noncomputable abbrev mA : Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 154 1 Blueprint.NativeSporadic.ONSeed1

noncomputable abbrev mB : Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 154 1 Blueprint.NativeSporadic.ONSeed2

private theorem seedA_eq' : Native.seedA = Blueprint.NativeSporadic.ONSeed1 := rfl

private theorem seedB_eq' : Native.seedB = Blueprint.NativeSporadic.ONSeed2 := rfl

theorem seedA_eq : Native.seedA = Blueprint.NativeSporadic.ONSeed1 := seedA_eq'

theorem seedB_eq : Native.seedB = Blueprint.NativeSporadic.ONSeed2 := seedB_eq'

theorem toMat_rowsA : toMat 154 rowsA = mA := by
  unfold rowsA; rw [toMat_rowsOf, seedA_eq]

theorem toMat_rowsB : toMat 154 rowsB = mB := by
  unfold rowsB; rw [toMat_rowsOf, seedB_eq]

theorem rowsWF_rowsA : RowsWF rowsA := RowsWF.rowsOf 154 Native.seedA

theorem rowsWF_rowsB : RowsWF rowsB := RowsWF.rowsOf 154 Native.seedB

theorem rowsOf_size (s : String) : (F3.Native.rowsOf 154 s).size = 154 := by
  unfold F3.Native.rowsOf; simp

theorem rowsA_size : rowsA.size = 154 := rowsOf_size _

theorem powM_facts {M : Array V} (hM : RowsWF M) : ∀ e : ℕ, (powM 154 M e).size = 154 ∧
    RowsWF (powM 154 M e) ∧ toMat 154 (powM 154 M e) = toMat 154 M ^ e
  | 0 => ⟨idM_size' 154, RowsWF.idM 154, by rw [powM, toMat_idM, pow_zero]⟩
  | e + 1 => by
    obtain ⟨hs, hw, ht⟩ := powM_facts hM e
    refine ⟨?_, RowsWF.mul _ 154 hw hM, ?_⟩
    · rw [powM]; unfold CFSG.F3.Native.mul; rw [Array.size_map, hs]
    · rw [powM, toMat_mul hs hw hM, ht, pow_succ]

end CFSG.Sporadic.ON
