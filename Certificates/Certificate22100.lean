module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4Inputs
import all CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4Inputs
public meta import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

open CFSG.ComponentClassification.GSThmB.Cat81A8

namespace CertificateChecks.Batch22100

open CFSG.ComponentClassification.GSThmB.Cat81A8

set_option maxHeartbeats 0 in
private theorem card_TList : TList.length = 128 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem closed_TList : closedUnder gensT TList = true := by
  decide +kernel

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
