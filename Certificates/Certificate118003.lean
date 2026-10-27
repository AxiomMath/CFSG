module

public import Certificates.Kernel.OmegaEight.Bridge3009
public import Certificates.Kernel.OmegaEight.Om0Gen118003K
public import Certificates.Certificate3119

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4.E4O8
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0Check

theorem om0_gen {i : Nat} (hi : i < 8) :
    genArrs[i]! = unpack 360 9 (AP.S i) ∧ cn (AP.S i) = true ∧ pm (AP.S i) = true ∧
      cn (pinv (AP.S i)) = true := by
  have hk := kOm0
  simp only [bAnd_iff] at hk
  have h := allN_spec hk.1 i hi
  simp only [bAnd_iff] at h
  have hs := kStrC
  simp only [bAnd_iff] at hs
  exact ⟨gen_get (by omega), allN_spec hs.1 i (by omega), h.1, h.2⟩

theorem om0Gen_k : om0GenCheck () = true := by
  have hk := kOm0
  simp only [bAnd_iff] at hk
  obtain ⟨-, hl, hv, hcomm, hprod⟩ := hk
  obtain ⟨ex, cx, -⟩ := main_ok (by norm_num : 0 < 5)
  have ex' : xA 0 = unpack 360 9 (mainK 0) := ex
  have ev : v0A () = unpack 360 9 om0V := omegaW_eq hl
  unfold om0GenCheck om0Comm om0Prod
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro l hl'
    have hl8 : l < 8 := by simp at hl'; omega
    obtain ⟨eg, cg, -, -⟩ := om0_gen hl8
    rw [eg, ex', compA_pc cg cx, compA_pc cx cg, eqA_pc (cn_pc cg cx) (cn_pc cx cg)]
    exact List.all_eq_true.1 hcomm l hl'
  · obtain ⟨e0, c0, p0, i0⟩ := om0_gen (by norm_num : 0 < 8)
    obtain ⟨e2, c2, p2, i2⟩ := om0_gen (by norm_num : 2 < 8)
    obtain ⟨e3, c3, p3, i3⟩ := om0_gen (by norm_num : 3 < 8)
    obtain ⟨e4, c4, p4, i4⟩ := om0_gen (by norm_num : 4 < 8)
    obtain ⟨e6, c6, p6, i6⟩ := om0_gen (by norm_num : 6 < 8)
    have cvx := cn_pc hv cx
    rw [e0, e2, e3, e4, e6, ex', ev, compA_pc hv cx, conjArr_cj c3 i3 p3 cx,
      conjArr_cj c0 i0 p0 hv, conjArr_cj c2 i2 p2 hv, conjArr_cj c4 i4 p4 hv,
      conjArr_cj c6 i6 p6 cvx, compA_pc (cn_cj c0 i0 hv) (cn_cj c2 i2 hv),
      compA_pc (cn_pc (cn_cj c0 i0 hv) (cn_cj c2 i2 hv)) (cn_cj c4 i4 hv),
      compA_pc (cn_pc (cn_pc (cn_cj c0 i0 hv) (cn_cj c2 i2 hv)) (cn_cj c4 i4 hv)) (cn_cj c6 i6 cvx),
      eqA_pc (cn_cj c3 i3 cx)
        (cn_pc (cn_pc (cn_pc (cn_cj c0 i0 hv) (cn_cj c2 i2 hv)) (cn_cj c4 i4 hv)) (cn_cj c6 i6 cvx))]
    exact hprod

end CertificateChecks.KernelO8

namespace Certificates

open CertificateChecks

theorem certificate118003 : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0Check.om0GenCheck () = true :=
  KernelO8.om0Gen_k

end Certificates
