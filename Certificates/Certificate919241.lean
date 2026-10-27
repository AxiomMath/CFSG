module

public import Certificates.Data.Foote82McLSylInvol
import Certificates.Kernel.Sporadic.McLC.Syl
import Certificates.Kernel.Sporadic.McLC.SqOne
import CFSG.Certificates.Kernel.J3C.Sound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.CentReg
  CFSG.KC.BfsPin
  CertificateChecks.KernelSpor CertificateChecks.KernelSpor.McLC CFSG.CGT.Foote82.Proof511.McLSyl

namespace CertificateChecks.Batch919241

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.CentReg
  CFSG.KC.BfsPin
  CertificateChecks.KernelSpor CertificateChecks.KernelSpor.McLC CFSG.CGT.Foote82.Proof511.McLSyl

theorem cntN_countP (n : Nat) (f : Nat → Bool) : cntN n f = (List.range n).countP f := by
  unfold cntN
  rw [Raw.Orb.foldN_eq, foldr_cnt f (List.range n) 0, Nat.zero_add, List.countP_eq_length_filter]

theorem ofFn_val {α : Type*} (n : Nat) (g : Nat → α) :
    List.ofFn (fun i : Fin n => g i.val) = (List.range n).map g := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp

theorem sqOneCount_eq : sqOneCount () = 36 := by
  unfold sqOneCount
  rw [closure_eq.1]
  simp only [hRec, Array.toList_ofFn]
  rw [ofFn_val McLCS.cnt (fun i => tabT (unpack 275 9 (McLCS.T i))), List.countP_map,
    ← Nat.eq_of_beq_eq_true sqOne_ok, cntN_countP]
  apply List.countP_congr
  intro i hi
  have hp := s_canon i (List.mem_range.1 hi)
  simp only [Function.comp_apply]
  rw [CertificateChecks.KernelSpor.McLC.invoOK_eq, compT_unpack hp hp, hid,
    tblEq_unpack (canonK_pcomp hp hp) sylBase.2.1]

end CertificateChecks.Batch919241

public section

namespace Certificates

open CertificateChecks

open CFSG.CGT.Foote82.Proof511.McLSyl in
theorem certificate919241 : sqOneCount () = 36 :=
  CertificateChecks.Batch919241.sqOneCount_eq

end Certificates

end
