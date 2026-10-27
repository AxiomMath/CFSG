module

public import Certificates.Data.A6EOne
import Certificates.Kernel.H13.A6EOneN
import CFSG.Certificates.Kernel.A6EOneNSound

namespace CertificateChecks.Batch7095

open CFSG.Quasithin.H13.A6EOne CertificateChecks.A6EOneNK

theorem hD : ∀ n, dc n = dec (DofT AP n) := dc_eq_DofT AP autL_eq

theorem chkX_of_keys (g : Grp)
    (h : CFSG.Decide.bitsetNodup ((xList g.I).map (CFSG.Decide.listKey 10 [0, 1, 2, 3])) = true) :
    g.chkX = true := by
  rw [Grp.chkX, decide_eq_true_eq]
  exact CFSG.Decide.nodup_of_bitsetNodup _ h

theorem chkWit_of (g : Grp) (h : g.chkWitN (DofT AP) = true) : g.chkWit = true := by
  rw [chkWit_eq g (DofT AP) hD]
  exact h

end CertificateChecks.Batch7095

namespace CertificateChecks.Batch7095

open CFSG.Quasithin.H13.A6EOne CertificateChecks.A6EOneNK

theorem grp0_check : grp0.check = true := by
  simp only [Grp.check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨chkX_of_keys grp0 g0XKeys, g0S⟩, g0Inv⟩, g0Close⟩, g0Cls⟩,
    chkWit_of grp0 g0WitN⟩, g0Words⟩

theorem grp1_check : grp1.check = true := by
  simp only [Grp.check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨chkX_of_keys grp1 g1XKeys, g1S⟩, g1Inv⟩, g1Close⟩, g1Cls⟩,
    chkWit_of grp1 g1WitN⟩, g1Words⟩

theorem grp2_check : grp2.check = true := by
  simp only [Grp.check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨chkX_of_keys grp2 g2XKeys, g2S⟩, g2Inv⟩, g2Close⟩, g2Cls⟩,
    chkWit_of grp2 g2WitN⟩, g2Words⟩

theorem grp3_check : grp3.check = true := by
  simp only [Grp.check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨chkX_of_keys grp3 g3XKeys, g3S⟩, g3Inv⟩, g3Close⟩, g3Cls⟩,
    chkWit_of grp3 g3WitN⟩, g3Words⟩

theorem grp4_check : grp4.check = true := by
  simp only [Grp.check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨chkX_of_keys grp4 g4XKeys, g4S⟩, g4Inv⟩, g4Close⟩, g4Cls⟩,
    chkWit_of grp4 g4WitN⟩, g4Words⟩

theorem checkAll_0 : checkAll = true := by
  simp only [checkAll, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨coset, grp0_check⟩, grp1_check⟩, grp2_check⟩, grp3_check⟩, grp4_check⟩

end CertificateChecks.Batch7095

public section

namespace Certificates

open CertificateChecks

theorem certificate7095 : CFSG.Quasithin.H13.A6EOne.checkAll = true := CertificateChecks.Batch7095.checkAll_0

end Certificates
