module

public import CFSG.Sporadic.Co1Patterson.AmalgamInputs
public import Certificates.Kernel.Co1P.Bray
public import Certificates.Kernel.Co1P.Chk21157
public import Certificates.Kernel.Co1P.Trees

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.KD.Co1P CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.Co1Patterson.Native

theorem wRows_eq {i : Nat} (hi : i < 270) : wRows i = unpackR 24 (wK i) := by
  have hj : i < (recsT orbQMasks).length + 1 := by rw [recsQ_len]; omega
  rw [wRows, wP, vtxR, conjA, orbQ_eq, bray_hs treeQ_ok _ hj, bray_his treeQ_ok _ hj, repX_eq,
    repXi_eq, iotaA_K]
  simp only [CFSG.KC.F2W.mul_unpackW]
  rfl

theorem amalgam : amalgamCheck = true := by
  have hj : 3940 < (recsT orbEMasks).length + 1 := by rw [recsE_len]; omega
  have h1 : orbE.c.pts[triRoots.getD 2 0]! = unpackR 24 (ptE 3940) := by
    rw [orbE_eq]
    exact bray_pts treeE_ok _ hj
  have h2 : mul CFSG.Sporadic.Co1Block.iotaARows (repRows 1) = unpackR 24 (mulWK AL (repK 1)) := by
    rw [iotaA_K, repRows_eq, CFSG.KC.F2W.mul_unpackW]
    rfl
  have h3 : mul (mul (gEl (gensKe.getD 4 0)) (wRows (triW.getD 2 0))) (gElInv (gensKe.getD 4 0)) =
      unpackR 24 (mulWK (mulWK (getL oneK GDS 94) (wK 64)) (getL oneK GDIS 94)) := by
    rw [gEl_eq, gElInv_eq, show triW.getD 2 0 = 64 from rfl, wRows_eq (by omega),
      CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
    rfl
  have h4 : wRows (triW.getD 0 0) = unpackR 24 (wK 128) := wRows_eq (by decide)
  have hk := CFSG.KC.TreeK.andB_true amal_chk
  unfold amalgamCheck
  rw [h1, h2, h3, h4, beq_unpack, beq_unpack, hk.1, hk.2]
  decide

open Certificates in
theorem c21157 : CFSG.Sporadic.Co1Patterson.Native.amalgamCheck = true := amalgam

end CertificateChecks.KernelCo1P

end
