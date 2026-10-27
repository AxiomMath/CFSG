
module

public import Certificates.Kernel.Co1M.W10070
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam
  CFSG.KC.SortTree CFSG.Sporadic.Co1.Module

theorem w70_t1a : chunksK (actC w70.R w70.K3 w70.K3i) (lenL w70.K3) (w70.reg (getL 0 w70.r1 2))
    w70.t1.tab 2835 576 w70.t1.wl w70.t1.wp w70.t1.B 0 30 = true := by quickRfl

theorem w70_t1b : chunksK (actC w70.R w70.K3 w70.K3i) (lenL w70.K3) (w70.reg (getL 0 w70.r1 2))
    w70.t1.tab 2835 576 w70.t1.wl w70.t1.wp w70.t1.B 30 30 = true := by quickRfl

theorem w70_t1c : chunksK (actC w70.R w70.K3 w70.K3i) (lenL w70.K3) (w70.reg (getL 0 w70.r1 2))
    w70.t1.tab 2835 576 w70.t1.wl w70.t1.wp w70.t1.B 60 29 = true := by quickRfl

theorem w70_t3 : chunksK (actC w70.R w70.K2 w70.K2i) (lenL w70.K2) (w70.reg (getL 0 w70.r3 2))
    w70.t3.tab 540 576 w70.t3.wl w70.t3.wp w70.t3.B 0 17 = true := by quickRfl

theorem w70_t1 : w70.t1.OK (actC w70.R w70.K3 w70.K3i) (lenL w70.K3) (w70.reg (getL 0 w70.r1 2))
    576 2835 := by
  refine ⟨Nat.le_of_ble_eq_true rfl, fun c hc => ?_⟩
  have hC : w70.t1.C = 89 := rfl
  rw [hC] at hc
  by_cases h1 : c < 30
  · simpa using chunks_spec w70_t1a c h1
  · by_cases h2 : c < 60
    · have := chunks_spec w70_t1b (c - 30) (by omega)
      rwa [Nat.add_sub_cancel' (by omega)] at this
    · have := chunks_spec w70_t1c (c - 60) (by omega)
      rwa [Nat.add_sub_cancel' (by omega)] at this

theorem ok70 : InvFamOK w70 where
  rA := w70_rA
  rB := w70_rB
  sA := w70_sA
  sB := w70_sB
  sC := w70_sC
  prog := w70_prog
  tr := w70_tr
  idx := w70_idx
  fix3 := w70_fix3
  fix1 := w70_fix1
  fix2 := w70_fix2
  fixK3 := w70_fixK3
  fix4 := w70_fix4
  inv := w70_inv
  roots := w70_roots
  rootAct := w70_rootAct
  vecs := w70_vecs
  t1 := w70_t1
  t2 := tree_ok (Nat.le_of_ble_eq_true rfl) w70_t2
  t3 := tree_ok (Nat.le_of_ble_eq_true rfl) w70_t3
  v1 := tree_ok (Nat.le_of_ble_eq_true rfl) w70_v1
  v0 := tree_ok (Nat.le_of_ble_eq_true rfl) w70_v0
  mem := w70_mem
  fixB := w70_fixB
  fixC := w70_fixC
  img := w70_img
  vb := tree_ok (Nat.le_of_ble_eq_true rfl) w70_vb
  vc := tree_ok (Nat.le_of_ble_eq_true rfl) w70_vc

end CertificateChecks.KernelCo1M

end
