module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4Inputs
import all CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4Inputs
public meta import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
import CFSG.Certificates.Kernel.PermCent.CVSound

public section

open CFSG.ComponentClassification.GSThmB.Cat81A8

namespace CertificateChecks.Batch22100

open CFSG.ComponentClassification.GSThmB.Cat81A8

set_option maxHeartbeats 0 in
private theorem card_TList : TList.length = 128 := by
  decide +kernel

section PackedBFS

open CFSG.Certificates.Kernel.PkCV

private noncomputable def bfsStepC (gens L : List (CV 8)) : List (CV 8) :=
  (L ++ L.flatMap fun a => gens.map fun g => a * g).dedup

private noncomputable def bfsC (gens : List (CV 8)) : ℕ → List (CV 8)
  | 0 => [1]
  | k + 1 => bfsStepC gens (bfsC gens k)

private theorem bfs_map (gens : List (CV 8)) : ∀ k, bfs (gens.map ev) k = (bfsC gens k).map ev
  | 0 => by simp [bfs, bfsC, ev_one]
  | k + 1 => by
    simp only [bfs, bfsC, bfsStep, bfsStepC]
    rw [bfs_map gens k, ← List.dedup_map_of_injective ev_injective]
    simp only [List.map_append, List.flatMap_map, List.map_flatMap, List.map_map,
      Function.comp_def, ofTab_eq, ev_mul]

private theorem closed_map (gens L : List (CV 8)) :
    closedUnder (gens.map ev) (L.map ev) =
      L.all fun a => gens.all fun g => L.any fun b => decide (a * g = b) := by
  unfold closedUnder
  simp only [List.all_map, Function.comp_def, ev_mul', List.contains_map, beq_ev]

private theorem map_cOf_ev' (L : List (Equiv.Perm (Fin 8))) : (L.map cOf).map ev = L := by
  simp only [List.map_map, Function.comp_def, ev_cOf, List.map_id']

set_option maxHeartbeats 0 in
private theorem closedC_TList :
    ((bfsC (gensT.map cOf) 8).all fun a => (gensT.map cOf).all fun g =>
      (bfsC (gensT.map cOf) 8).any fun b => decide (a * g = b)) = true := by
  decide +kernel

private theorem closed_TList : closedUnder gensT TList = true := by
  have hT : TList = (bfsC (gensT.map cOf) 8).map ev := by
    unfold TList
    conv_lhs => rw [← map_cOf_ev' gensT]
    exact bfs_map _ 8
  have h := closed_map (gensT.map cOf) (bfsC (gensT.map cOf) 8)
  rw [map_cOf_ev' gensT, ← hT] at h
  rw [h]
  exact closedC_TList

end PackedBFS

set_option maxHeartbeats 0 in
private theorem bigInv_le : bigInv.length ≤ 3 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem lx_mem : lx ∈ TList := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem ly_mem : ly ∈ TList := by
  decide +kernel

private theorem lq_sq : (tr * tw) * (tr * tw) = lq := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem card_x : (bfs [lx, lq] 6).length = 16 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem card_y : (bfs [ly, lq] 6).length = 16 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem card_xy : (bfs [lx * ly, lq] 6).length = 16 := by
  decide +kernel

end CertificateChecks.Batch22100

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GSThmB.Cat81A8 in
theorem certificate22100 : TList.length = 128
    ∧ closedUnder gensT TList = true
    ∧ bigInv.length ≤ 3
    ∧ lx ∈ TList ∧ ly ∈ TList ∧ (tr * tw) * (tr * tw) = lq
    ∧ (bfs [lx, lq] 6).length = 16 ∧ (bfs [ly, lq] 6).length = 16
    ∧ (bfs [lx * ly, lq] 6).length = 16 :=
  ⟨CertificateChecks.Batch22100.card_TList, CertificateChecks.Batch22100.closed_TList, CertificateChecks.Batch22100.bigInv_le, CertificateChecks.Batch22100.lx_mem,
    CertificateChecks.Batch22100.ly_mem, CertificateChecks.Batch22100.lq_sq, CertificateChecks.Batch22100.card_x, CertificateChecks.Batch22100.card_y,
    CertificateChecks.Batch22100.card_xy⟩

end Certificates
