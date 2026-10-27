module

public import Certificates.Data.SmithB45ExcHSData
import Certificates.Kernel.B45.C260390K
import Certificates.Data.Kernel.B45Perm.Defs
import Certificates.Data.SmithB45ExcRuData
import Certificates.Kernel.LocalQT.SV.C4126T
import Certificates.Kernel.SporSch.Ru.Gens
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.LocalQT.SV.C4126
import CFSG.Certificates.Kernel.B45PermSound
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

namespace CertificateChecks.Batch260390

open CFSG.KS.Raw CFSG.KC.B45P CFSG.KC.PkPow CFSG.Quasithin.B45Exc.HS
  CFSG.Quasithin.B45Exc.Tab CFSG.QuasithinUnique.Bridge.HSExcl CFSG.KD.LQT.C4126

theorem hs_class0 : hsClassCheck0 = true := by
  unfold hsClassCheck0 hsInvProd hsGens
  rw [gens_eq, tp_eq (k := 5) (by norm_num)]
  exact b45OrdK_sound CFSG.KD.B45.C260390.hs0K

theorem hs_class1 : hsClassCheck1 = true := by
  unfold hsClassCheck1 hsInvProd hsGens
  rw [gens_eq, tp_eq (k := 12) (by norm_num)]
  exact b45CfgK_sound CFSG.KD.B45.C260390.hs1K

theorem hs_class3 : hsClassCheck3 = true := by
  unfold hsClassCheck3 hsInvProd hsGens
  rw [gens_eq, tp_eq (k := 34) (by norm_num)]
  exact b45CfgK_sound CFSG.KD.B45.C260390.hs3K

theorem ta_eq {k : Nat} (hk : k < 43) : hsTA k = unpack 3850 12 (HC.F k) := by
  unfold hsTA
  exact hsCentTbl_eq hk

theorem hs_fix : hsFixCheck = true := by
  have f5 := CFSG.KD.B45.C260390.hsFix5K
  have f12 := CFSG.KD.B45.C260390.hsFix12K
  have f21 := CFSG.KD.B45.C260390.hsFix21K
  have f34 := CFSG.KD.B45.C260390.hsFix34K
  unfold hsFixCheck
  rw [ta_eq (k := 5) (by norm_num), ta_eq (k := 12) (by norm_num), ta_eq (k := 21) (by norm_num),
    ta_eq (k := 34) (by norm_num), ← nfix_eq, ← nfix_eq, ← nfix_eq, ← nfix_eq,
    Nat.eq_of_beq_eq_true f5, Nat.eq_of_beq_eq_true f12, Nat.eq_of_beq_eq_true f21,
    Nat.eq_of_beq_eq_true f34]
  rfl

end CertificateChecks.Batch260390

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.B45Exc.HS in
theorem certificate260390 : hsClassCheck0 = true ∧ hsClassCheck1 = true ∧ hsClassCheck3 = true ∧ hsFixCheck = true :=
  ⟨CertificateChecks.Batch260390.hs_class0, CertificateChecks.Batch260390.hs_class1, CertificateChecks.Batch260390.hs_class3, CertificateChecks.Batch260390.hs_fix⟩

end Certificates
