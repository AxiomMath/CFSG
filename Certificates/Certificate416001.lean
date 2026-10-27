module

public import Certificates.Data.TwinE4Sp62S
import Certificates.Kernel.PermCent.K416001
public import Certificates.Data.Kernel.PermCent.CV
import CFSG.Certificates.Kernel.PermCent.CVSound

public section

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.Certificates CFSG.Certificates.Kernel.PkCV
  CFSG.ClassicalInvolution.Q3.TL4.Z2W.Sp62S CFSG.Certificates.Kernel.PkCV.Sp6B

namespace Certificates

open CertificateChecks

private theorem enum_ev416001 (Q : RawSchreierDatum 36) : enumeration Q = (elemsC Q).map ev :=
  (elemsT_eq Q).symm.trans (elemsT_eq_elemsC Q)

private theorem sqRoots_ev416001 (c : CV 36) (L : List (CV 36)) :
    sqRoots (ev c) (L.map ev) = (sqRootsC c L).map ev := by
  rw [sqRoots.eq_1, sqRootsC.eq_1, List.filter_map, List.map_map]
  simp only [Function.comp_def, tab_eq, ev_mul', decide_ev_eq]

private theorem sqStep_ev416001 (S : List (CV 36)) (s : CV 36) :
    sqStep (S.map ev) (ev s) = sqStepC S s := by
  rw [sqStep.eq_1, sqStepC.eq_1]
  simp only [List.all_map, List.filter_map, Function.comp_def, ev_mul', ev_inv', decide_ev_eq]

private theorem sqCheck_ev416001 (c : CV 36) (L : List (CV 36)) :
    sqCheck (ev c) (L.map ev) = sqCheckC c L := by
  rw [sqCheck.eq_1, sqCheckC.eq_1, sqRoots_ev416001]
  simp only [List.isEmpty_map, List.all_map, Function.comp_def, tab_eq, sqStep_ev416001, ev_mul',
    one_eq_ev, decide_ev_eq]

theorem certificate416001 : CFSG.ClassicalInvolution.Q3.TL4.Z2W.Sp62S.sPropCheck () = true := by
  rw [sPropCheck.eq_1, tab_eq, tab_eq, tab_eq, tab_eq, enum_ev416001, enum_ev416001,
    enum_ev416001, enum_ev416001, eq_ev_cOf sp6Rep1, eq_ev_cOf sp6Rep2, eq_ev_cOf sp6Rep3,
    eq_ev_cOf sp6Rep4, sqCheck_ev416001, sqCheck_ev416001, sqCheck_ev416001, sqCheck_ev416001]
  have h1 := KernelPermCent.k416001_1
  have h2 := KernelPermCent.k416001_2
  have h3 := KernelPermCent.k416001_3
  have h4 := KernelPermCent.k416001_4
  rw [sq1C.eq_1] at h1
  rw [sq2C.eq_1] at h2
  rw [sq3C.eq_1] at h3
  rw [sq4C.eq_1] at h4
  simp only [h1, h2, h3, h4, Bool.and_self]

end Certificates
