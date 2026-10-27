module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiInputs
import Certificates.Kernel.I242.Gens
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

namespace CertificateChecks.Batch13522

open CFSG.KC.Enum CFSG.KC.I242 CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CertificateChecks.KernelI242
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Fischer

theorem pow2_eq (t : Array Nat) : powA 3510 t 2 = compA 3510 t (compA 3510 t (idA 3510)) := rfl

theorem scalar_of {G Q1 Q2 : Nat} (hG : cn G = true) (h1 : cn Q1 = true) (h2 : cn Q2 = true)
    (hid : cn pid = true) (eG : fi22ScalarArr = unpack 3510 12 G)
    (e1 : fi22FiveQ1Arr = unpack 3510 12 Q1) (e2 : fi22FiveQ2Arr = unpack 3510 12 Q2)
    (h : (Nat.beq (pc G Q1) (pc (pc Q1 (pc Q1 pid)) G) &&
      Nat.beq (pc G Q2) (pc (pc Q2 (pc Q2 pid)) G)) = true) :
    fi22ScalarCheck = true := by
  unfold fi22ScalarCheck
  rw [pow2_eq, pow2_eq, eG, e1, e2, idA_eq, compA_pc hG h1, compA_pc hG h2, compA_pc h1 hid,
    compA_pc h1 (cn_pc h1 hid), compA_pc h2 hid, compA_pc h2 (cn_pc h2 hid),
    compA_pc (cn_pc h1 (cn_pc h1 hid)) hG, compA_pc (cn_pc h2 (cn_pc h2 hid)) hG,
    eqA_unpack (cn_pc hG h1) (cn_pc (cn_pc h1 (cn_pc h1 hid)) hG),
    eqA_unpack (cn_pc hG h2) (cn_pc (cn_pc h2 (cn_pc h2 hid)) hG)]
  exact h

noncomputable def GK : Nat :=
  pc (pc (aK H.F AK 3) (bK H.F 3)) (pc (aK H.F AK 4) (bK H.F 4))

theorem gk_canon : cn GK = true ∧ fi22ScalarArr = unpack 3510 12 GK := by
  have p3 := parts_ok (i := 3) (by decide)
  have p4 := parts_ok (i := 4) (by decide)
  have a3 := (cpK_iff p3.2.1).1
  have b3 := (cpK_iff p3.2.2).1
  have a4 := (cpK_iff p4.2.1).1
  have b4 := (cpK_iff p4.2.2).1
  refine ⟨cn_pc (cn_pc a3 b3) (cn_pc a4 b4), ?_⟩
  unfold fi22ScalarArr GK
  rw [cA_eq (i := 3) (by decide), cB_eq (i := 3) (by decide), cA_eq (i := 4) (by decide),
    cB_eq (i := 4) (by decide), compA_pc a3 b3, compA_pc a4 b4,
    compA_pc (cn_pc a3 b3) (cn_pc a4 b4)]

theorem kCn : (cn (H.F 0) && cn pid) = true := by quickRfl

theorem kScalar : (Nat.beq (pc GK (H.F 0)) (pc (pc (H.F 0) (pc (H.F 0) pid)) GK) &&
    Nat.beq (pc GK (H.F 1)) (pc (pc (H.F 1) (pc (H.F 1) pid)) GK)) = true := by quickRfl

theorem check : fi22ScalarCheck = true := by
  have hc := kCn
  simp only [Bool.and_eq_true] at hc
  exact scalar_of gk_canon.1 hc.1 q2_cn hc.2 gk_canon.2 (fiveArr_eq (k := 0) (by decide))
    (fiveArr_eq (k := 1) (by decide)) kScalar

end CertificateChecks.Batch13522

public section

namespace Certificates

open CertificateChecks

theorem certificate13522 : CFSG.HardMathSupport.Solomon.Coordinator.fi22ScalarCheck = true :=
  CertificateChecks.Batch13522.check

end Certificates
