module

public import CFSG.Sporadic.Co1.Module.CoTwoChain
public import Certificates.Data.CFSGNative.Co1.U6OddData
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.U6OddData
public import Certificates.Certificate3024
public import CFSG.Sporadic.Co1.Module.CoTwoData
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10067
public import Certificates.Kernel.Co1B.Tri2045

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.U6Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.CoTwoNative CFSG.Sporadic.Co1.U6OddNative Matrix

@[expose] def initRows : Array (Array ℕ) := #[dat.rowsA, dat.rowsB]

@[expose] def regsRows : Array (Array ℕ) := runRows initRows prog

@[expose] def rr (i : ℕ) : Array ℕ := regsRows[i]?.getD (idRows 24)

noncomputable def regsG :
    List NativeSporadic.Co1 := Odd.runEval [Odd.eA, Odd.eB] prog

noncomputable def regG (i : ℕ) : NativeSporadic.Co1 := regsG.getD i 1

theorem regs_rel : Odd.RegsRel Odd.mat regsG regsRows := by
  refine Odd.runRows_spec Odd.mat prog ?_
  refine ⟨rfl, fun i => ?_⟩
  match i with
  | 0 => exact Odd.mat_eA
  | 1 => exact Odd.mat_eB
  | i + 2 => simp [rowsMatrix_idRows, initRows]

section

attribute [local irreducible] regsG regsRows

theorem mat_reg
    (i : ℕ) : Odd.mat (regG i) = rowsMatrix 24 (rr i) := by
  have h : ∀ j : ℕ, Odd.mat (regsG.getD j 1) =
      rowsMatrix 24 (regsRows[j]?.getD (idRows 24)) :=
    And.right regs_rel
  simpa only [regG, rr] using h i

end

end CFSG.Sporadic.Co1.Module.U6Odd
