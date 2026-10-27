module

public import Certificates.Data.ParrottSpin
import Certificates.Kernel.Direct.C946006

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.GF2n.Parrott

structure SpinFacts : Prop where
  Ms1_cube : Ms1 * Ms1 * Ms1 = 1
  Ms2_cube : Ms2 * Ms2 * Ms2 = 1
  Ms1s2_cube : Ms1s2 * Ms1s2 * Ms1s2 = 1
  Ms1s2inv_cube : Ms1s2inv * Ms1s2inv * Ms1s2inv = 1
  Mt_sq : Mt * Mt = 1
  Mu_sq : Mu * Mu = 1
  Mv_sq : Mv * Mv = 1
  fix_s1 : fixDim Ms1 = 2
  fix_s2 : fixDim Ms2 = 2
  fix_s1s2 : fixDim Ms1s2 = 0
  fix_s1s2inv : fixDim Ms1s2inv = 4
  fix_t : fixDim Mt = 6
  fix_u : fixDim Mu = 6
  fix_v : fixDim Mv = 4
  card_fix_s1 : fixCard Ms1 = 4
  card_fix_s2 : fixCard Ms2 = 4
  card_fix_s1s2 : fixCard Ms1s2 = 1
  card_fix_s1s2inv : fixCard Ms1s2inv = 16
  card_fix_t : fixCard Mt = 64
  card_fix_u : fixCard Mu = 64
  card_fix_v : fixCard Mv = 16
  q_inv_s1 : ∀ v : V, q (Ms1.mulVec v) = q v
  q_inv_s2 : ∀ v : V, q (Ms2.mulVec v) = q v
  q_inv_s1s2 : ∀ v : V, q (Ms1s2.mulVec v) = q v
  q_inv_s1s2inv : ∀ v : V, q (Ms1s2inv.mulVec v) = q v
  q_inv_t : ∀ v : V, q (Mt.mulVec v) = q v
  q_inv_u : ∀ v : V, q (Mu.mulVec v) = q v
  q_inv_v : ∀ v : V, q (Mv.mulVec v) = q v
  b_nondegenerate : ∀ v : V, (∀ w : V, b v w = 0) → v = 0
  rel_a2 : ∀ e : Fin 8, bitWord spinRelA2 (1 <<< (e : Nat)) = 1 <<< (e : Nat)
  rel_b5 : ∀ e : Fin 8, bitWord spinRelB5 (1 <<< (e : Nat)) = 1 <<< (e : Nat)
  rel_ab9 : ∀ e : Fin 8, bitWord spinRelAB9 (1 <<< (e : Nat)) = 1 <<< (e : Nat)
  rel_comm3 : ∀ e : Fin 8, bitWord spinRelComm3 (1 <<< (e : Nat)) = 1 <<< (e : Nat)
  rel_comm_bab2 : ∀ e : Fin 8, bitWord spinRelCommBab2 (1 <<< (e : Nat)) = 1 <<< (e : Nat)

end Certificates

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelDirect.C946006 in
open CFSG.RankThree.GF2n.Parrott in
theorem certificate946006 : SpinFacts := {
    Ms1_cube, Ms2_cube, Ms1s2_cube, Ms1s2inv_cube, Mt_sq, Mu_sq, Mv_sq,
    fix_s1, fix_s2, fix_s1s2, fix_s1s2inv, fix_t, fix_u, fix_v,
    card_fix_s1, card_fix_s2, card_fix_s1s2, card_fix_s1s2inv, card_fix_t, card_fix_u, card_fix_v,
    q_inv_s1, q_inv_s2, q_inv_s1s2, q_inv_s1s2inv, q_inv_t, q_inv_u, q_inv_v,
    b_nondegenerate, rel_a2, rel_b5, rel_ab9, rel_comm3, rel_comm_bab2 }

end Certificates
