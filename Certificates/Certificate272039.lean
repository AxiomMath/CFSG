module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.J2ModelData
import CFSG.Certificates.Kernel.J2ModelKSound
import Certificates.Kernel.J2Model.Check
import Certificates.Kernel.J2Cover.Orb
import Certificates.Kernel.Sporadic.J2K.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P CFSG.KC.J2ModelK CertificateChecks.KernelJ2Cover
open CFSG.Sporadic.Th.Native

theorem certificate272039 : CFSG.Quasithin.Kleidman.ThreeLocal.J2Model.j2ModelCheck = true := by
  have j2_tab_eq : ∀ P : Nat, (Array.ofFn (n := 315) fun i => UInt32.ofNat (pg 9 511 P i.val)) =
      CFSG.KC.Child3.tabP 315 9 P := by
    intro P
    simp only [CFSG.KC.Child3.tabP, CFSG.ComponentClassification.J2Cover.arrTable]
    refine congrArg (Array.ofFn (n := 315)) (funext fun i => ?_)
    rw [CFSG.KC.Child3.unpack_get' i.isLt]
    rfl
  have hsz : CFSG.KS.Raw.szOK 315 9 = true := by rfl
  have hA := CFSG.KC.Misc.ArrEnum.pp_of_permB hsz KernelJ2Model.permA
  have hB := CFSG.KC.Misc.ArrEnum.pp_of_permB hsz KernelJ2Model.permB'
  have hsize : (CFSG.Sporadic.J2.Native.orbitData ()).pts.size = 315 := by
    rw [KernelSpor.J2K.orb_eq.1]
    exact KernelSpor.J2K.size_OJ
  have hal : (CFSG.Sporadic.J2.Native.orbitData ()).alpha = CFSG.KC.Child3.tabP 315 9 ALP := by
    rw [alpha_eq, j2_tab_eq]
  have hbe : (CFSG.Sporadic.J2.Native.orbitData ()).beta = CFSG.KC.Child3.tabP 315 9 BEP := by
    rw [beta_eq, j2_tab_eq]
  have hgen : ∀ z, CFSG.Sporadic.J1.Native.genTables (CFSG.Sporadic.J2.Native.orbitData ()) z =
      CFSG.KC.Child3.tabP 315 9 (genK 315 9 ALP BEP z) := by
    intro z
    unfold CFSG.Sporadic.J1.Native.genTables genK
    rw [hsize, hal, hbe]
    split_ifs
    · rfl
    · exact invT_tabP hA
    · rfl
    · exact invT_tabP hB
  unfold CFSG.Quasithin.Kleidman.ThreeLocal.J2Model.j2ModelCheck
  simp only [hsize, decide_true, Bool.true_and]
  exact modelCheckAt_of_modelK hsz hgen KernelJ2Model.chk

end Certificates
