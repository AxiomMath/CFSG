module

public import Certificates.Data.SmithB45MatGen
import Certificates.Kernel.B45.C260401K
import Certificates.Data.Kernel.B45Perm.GenW
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.LocalQT.Syl.C4059
import Certificates.Kernel.LocalQT.Syl.C4037
import Certificates.Kernel.LocalQT.Syl.C4057
import Certificates.Kernel.LocalQT.Syl.C4069
import CFSG.Certificates.Kernel.B45GenWSound

namespace CertificateChecks.Batch260401

open CFSG.KC.B45P CFSG.KC.LQT.Syl CFSG.KC.LQT.Syl.Pf CFSG.Quasithin.B45Mat
  CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Blueprint

theorem gen24 : genWitOK NativeSporadic.M24 m24rl m24a m24b m24GenTab = true := by
  have h := CFSG.KD.B45.C260401.g24K
  rw [rlK_eq m24a m24b (by norm_num) CFSG.KD.LQT.C4059.hA CFSG.KD.LQT.C4059.hB] at h
  exact genWK_sound (by norm_num) _ m24a m24b CFSG.KD.LQT.C4059.hA CFSG.KD.LQT.C4059.hB _ h

theorem gen23 : genWitOK NativeSporadic.M23 m23rl m23GenA m23GenB m23GenTab = true := by
  have h := CFSG.KD.B45.C260401.g23K
  rw [rlK_eq m23GenA m23GenB (by norm_num) CFSG.KD.LQT.C4037.hA CFSG.KD.LQT.C4037.hB] at h
  exact genWK_sound (by norm_num) _ m23GenA m23GenB CFSG.KD.LQT.C4037.hA CFSG.KD.LQT.C4037.hB _ h

theorem gen22 : genWitOK NativeSporadic.M22 m22rl m22a m22b m22GenTab = true := by
  have h := CFSG.KD.B45.C260401.g22K
  rw [rlK_eq m22a m22b (by norm_num) CFSG.KD.LQT.C4057.hA CFSG.KD.LQT.C4057.hB] at h
  exact genWK_sound (by norm_num) _ m22a m22b CFSG.KD.LQT.C4057.hA CFSG.KD.LQT.C4057.hB _ h

theorem gen12 : genWitOK NativeSporadic.M12 m12rl m12a m12b m12GenTab = true := by
  have h := CFSG.KD.B45.C260401.g12K
  rw [rlK_eq m12a m12b (by norm_num) CFSG.KD.LQT.C4069.hA CFSG.KD.LQT.C4069.hB] at h
  exact genWK_sound (by norm_num) _ m12a m12b CFSG.KD.LQT.C4069.hA CFSG.KD.LQT.C4069.hB _ h

end CertificateChecks.Batch260401

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.B45Mat CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Mathieu
  CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate260401 :
    genWitOK NativeSporadic.M24 m24rl m24a m24b m24GenTab = true ∧
    genWitOK NativeSporadic.M23 m23rl m23GenA m23GenB m23GenTab = true ∧
    genWitOK NativeSporadic.M22 m22rl m22a m22b m22GenTab = true ∧
    genWitOK NativeSporadic.M12 m12rl m12a m12b m12GenTab = true :=
  ⟨CertificateChecks.Batch260401.gen24, CertificateChecks.Batch260401.gen23, CertificateChecks.Batch260401.gen22, CertificateChecks.Batch260401.gen12⟩

end Certificates
