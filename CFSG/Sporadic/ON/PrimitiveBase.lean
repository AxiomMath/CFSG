
module

public import CFSG.Sporadic.ON.SetupBase

@[expose] public section

namespace CFSG.Sporadic.ON

open Native Matrix
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (inTreeB labelsOf)

theorem ap_lineLetters {L : Array Table} {R Lf : Table} {l : ℕ} (hl : l < L.size) {j : ℕ}
    (hj : j < nLines) : ap (lineLetters L R Lf)[l]! j = ap Lf (ap L[l]! (ap R j)) := by
  unfold lineLetters
  rw [getElem!_pos (L.map _) l (by simpa using hl), Array.getElem_map, ap_ofFn _ hj,
    getElem!_pos L l hl]
  rfl

theorem ap_lineL {l : ℕ} (hl : l < letters.size) {j : ℕ} (hj : j < nLines) :
    ap lineL[l]! j = ap lineT (ap letters[l]! (ap reps j)) :=
  ap_lineLetters hl hj

@[expose] def subSizesF : Fin 5 → ℕ := ![1, 5586, 58653, 52136, 6384]

theorem subSizes_getElem (i : Fin 5) : subSizes[i.val]! = subSizesF i := by
  revert i; decide

set_option maxRecDepth 10000 in
theorem subSizes_blocks : ∀ S : Finset (Fin 5), (0 : Fin 5) ∈ S →
    (∑ i ∈ S, subSizesF i) ∣ 122760 → S = {0} ∨ S = Finset.univ := by
  decide

end CFSG.Sporadic.ON
