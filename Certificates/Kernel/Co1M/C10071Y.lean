module

public import Certificates.Kernel.Co1M.C10071Z
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KD.Co1Odd CFSG.Sporadic.Co1.Module.Odd CFSG.Sporadic.Co1.OddNative

theorem c71_zTwo : zTwoLitOK := by
  have hg := z71_gens
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  have ht := z71_tree2
  simp only [Bool.and_eq_true] at ht
  refine ⟨?_, ht.1.1, ht.1.2, ht.2⟩
  rw [hg.2]
  have e : zIdx[2]! = [83, 84] := rfl
  rw [e, List.map_cons, List.map_cons, List.map_nil, c71_rr (by rw [c71_len]; norm_num),
    c71_rr (by rw [c71_len]; norm_num)]
  rfl

theorem c71_orbitY : orbitYLitOK = true := by
  unfold orbitYLitOK yList w2List
  rw [c71_W2, c71_isT2f]
  quickRfl

theorem c71_rr27 : rr 27 = unpackR 24 (getL 0 cmRP71 27) := c71_rr (by rw [c71_len]; norm_num)

theorem c71_rr76 : rr 76 = unpackR 24 (getL 0 cmRP71 76) := c71_rr (by rw [c71_len]; norm_num)

theorem c71_outer : outerLitOK = true := by
  have e2 : sIdx[2]! = 76 := rfl
  unfold outerLitOK outerTest Mt
  rw [e2, c71_rr27, c71_rr76, c71_isT4f]
  quickRfl

end CertificateChecks.KernelCo1M

end
