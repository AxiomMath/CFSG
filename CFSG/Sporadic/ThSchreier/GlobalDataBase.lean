
module

public import CFSG.Sporadic.ThSchreier.LocalOrbitBase
public import CFSG.Sporadic.Schreier.LyBFS

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.LySchreier
  Pointwise

noncomputable abbrev planeWSet : Set RowV := (planeW : Set RowV)

@[expose] noncomputable def matRows (X : Matrix (Fin 248) (Fin 248) (ZMod 2)) : Array V4 :=
  Array.ofFn fun i : Fin 248 => V4.ofFn fun j => if h : j < 248 then X i ⟨j, h⟩ = 1 else false

theorem frApply_matRows_wf (X : Matrix (Fin 248) (Fin 248) (ZMod 2)) (v : V4) :
    (frApply (frTable (matRows X)) v).wf = true := by
  refine frApply_frTable_wf (fun r hr => ?_) v
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hr
  exact V4.ofFn_wf _

theorem wKeyRow_canonical : wKeyRow.isCanonical = true := by
  unfold wKeyRow
  refine canon_isCanonical (v4OfNat_wf (by norm_num)) (v4OfNat_wf (by norm_num)) ?_ ?_ ?_
  · rw [toVec_v4OfNat]; exact wRow1_ne_zero
  · rw [toVec_v4OfNat]; exact wRow2_ne_zero
  · rw [toVec_v4OfNat, toVec_v4OfNat]; exact wRow1_ne_wRow2

end CFSG.Sporadic.ThSchreier
