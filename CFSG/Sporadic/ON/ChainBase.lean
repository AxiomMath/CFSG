
module

public import CFSG.Sporadic.ON.SetupBase

@[expose] public section

namespace CFSG.Sporadic.ON

open Native Matrix
open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (lettersOf instrLt ordOK inTreeB labelsOf)

theorem nPts_lt : nPts < 2 ^ 32 := by norm_num

theorem regsT_size : regsT.size = nregs := by simp [regsT, regs0]

theorem regsT_get {r : ℕ} (hr : r < nregs) : regsT[r]! =
    if r = 0 then wordT nPts (genT orb) wordA else if r = 1 then
      wordT nPts (genT orb) wordB else idT nPts := by
  rw [getElem!_pos regsT r (by rw [regsT_size]; exact hr)]
  simp only [regsT, regs0, Array.getElem_ofFn]

theorem letters_size : letters.size = 2 * sel.size := by simp [letters, lettersOf]

theorem chainBase_size : chainBase.size = 3 := rfl

theorem trees_size : trees.size = 3 := by simp [trees, chainTrees, chainBase_size]

theorem chainBase_zero : chainBase[0]! = 0 := rfl

noncomputable abbrev root : Fin nPts := ⟨0, by norm_num⟩

end CFSG.Sporadic.ON
