module

public import Certificates.Kernel.ChengHeld.PropsAutF
public import Certificates.Kernel.ChengHeld.PropsEA
public import Certificates.Kernel.ChengHeld.PropsS2
public import CFSG.Certificates.Kernel.ChengHeldPropsEASound
public import CFSG.Certificates.Kernel.ChengHeldS2StructSound

public section

namespace CertificateChecks.KernelChengHeld.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model CFSG.KC.ChengHeldS2
open CFSG.KC.ChengHeldP CertificateChecks.KernelChengHeld

theorem ea2 : (mkReg 2).eaCounts = [55, 303, 309, 62, 2, 0] := by
  have hd := regData (α := 2) (by norm_num) chPres_true
  have hB := bound2
  rw [mkReg_eq] at hB ⊢
  have hW := rows_of hB
  have i := p6138_ea2i
  have u := p6138_ea2u
  have w := p6138_ea2w
  have z := p6138_eaz
  simp only [bAnd_iff] at i u w z
  have l1 := levelOK_one hd.rep hW i.1 i.2.2
  have l2 := levelOK_succ hd.rep hW i.1 i.2.1 l1 u.1 w.1
  have l3 := levelOK_succ hd.rep hW i.1 i.2.1 l2 u.2.1 w.2.1
  have l4 := levelOK_succ hd.rep hW i.1 i.2.1 l3 u.2.2.1 w.2.2.1
  have l5 := levelOK_succ hd.rep hW i.1 i.2.1 l4 u.2.2.2 w.2.2.2.1
  have l6 := levelOK_succ hd.rep hW i.1 i.2.1 l5 z.2.2 w.2.2.2.2
  exact eaCounts_of hd.rep (L := fun k => EAL2 k)
    (c := fun k => [55, 303, 309, 62, 2, 0].getD k 0) fun k hk => by
      interval_cases k
      exacts [l1, l2, l3, l4, l5, l6]

theorem struct2 : struct2OK = true := by
  have hd := regData (α := 2) (by norm_num) chPres_true
  have R : Rep (mkReg 2) ↥(permGroup (regN 2) (permOf 2) (regGens 2).size) := by
    rw [mkReg_eq]
    exact hd.rep
  exact struct2OK_of R bound2.tree bound2.N_eq bound2.m_eq bound2.inv_eq bound2.g_eq
    (by norm_num) (mlt_of (by norm_num) bound2) rfl p6138_s2cl p6138_s2cm ea2 p6138_s2

end CertificateChecks.KernelChengHeld.P

end
