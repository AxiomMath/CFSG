module

public import Certificates.Data.ParrottSpin

public section

namespace CertificateChecks.KernelDirect.C946006

open CFSG.RankThree.GF2n.Parrott

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem Ms1_cube : Ms1 * Ms1 * Ms1 = 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem Ms2_cube : Ms2 * Ms2 * Ms2 = 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem Ms1s2_cube : Ms1s2 * Ms1s2 * Ms1s2 = 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem Ms1s2inv_cube : Ms1s2inv * Ms1s2inv * Ms1s2inv = 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem Mt_sq : Mt * Mt = 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem Mu_sq : Mu * Mu = 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem Mv_sq : Mv * Mv = 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fix_s1 : fixDim Ms1 = 2 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fix_s2 : fixDim Ms2 = 2 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fix_s1s2 : fixDim Ms1s2 = 0 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fix_s1s2inv : fixDim Ms1s2inv = 4 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fix_t : fixDim Mt = 6 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fix_u : fixDim Mu = 6 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fix_v : fixDim Mv = 4 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_s1 : fixCard Ms1 = 4 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_s2 : fixCard Ms2 = 4 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_s1s2 : fixCard Ms1s2 = 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_s1s2inv : fixCard Ms1s2inv = 16 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_t : fixCard Mt = 64 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_u : fixCard Mu = 64 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_v : fixCard Mv = 16 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem q_inv_s1 : ∀ v : V, q (Ms1.mulVec v) = q v := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem q_inv_s2 : ∀ v : V, q (Ms2.mulVec v) = q v := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem q_inv_s1s2 : ∀ v : V, q (Ms1s2.mulVec v) = q v := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem q_inv_s1s2inv : ∀ v : V, q (Ms1s2inv.mulVec v) = q v := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem q_inv_t : ∀ v : V, q (Mt.mulVec v) = q v := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem q_inv_u : ∀ v : V, q (Mu.mulVec v) = q v := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem q_inv_v : ∀ v : V, q (Mv.mulVec v) = q v := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem b_nondegenerate : ∀ v : V, (∀ w : V, b v w = 0) → v = 0 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rel_a2 : ∀ e : Fin 8, bitWord spinRelA2 (1 <<< (e : Nat)) = 1 <<< (e : Nat) := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rel_b5 : ∀ e : Fin 8, bitWord spinRelB5 (1 <<< (e : Nat)) = 1 <<< (e : Nat) := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rel_ab9 : ∀ e : Fin 8, bitWord spinRelAB9 (1 <<< (e : Nat)) = 1 <<< (e : Nat) := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rel_comm3 : ∀ e : Fin 8, bitWord spinRelComm3 (1 <<< (e : Nat)) = 1 <<< (e : Nat) := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rel_comm_bab2 :
    ∀ e : Fin 8, bitWord spinRelCommBab2 (1 <<< (e : Nat)) = 1 <<< (e : Nat) := by
  decide +kernel

end CertificateChecks.KernelDirect.C946006
