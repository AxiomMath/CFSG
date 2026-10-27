module

public import Certificates.Data.Sz8CoverInvolutions
public import CFSG.LieType.Multipliers.Sz8Inputs
import Certificates.Kernel.Multipliers.Sz8Upper
import Certificates.Kernel.Misc.Coset.C7262M
import Certificates.Kernel.Misc.Coset.XSz8HA.Inv7262
import CFSG.LieType.Multipliers.Sz8Bridge

public section

namespace CertificateChecks.Batch7262

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8 CFSG.CosetTable CFSG.KC.MiscCoset
  CFSG.Certificates.CosetEnumeration

theorem lift_genSz_centWords : ∀ w ∈ centWords, FreeGroup.lift genSz (FreeGroup.mk w) = 1 := by
  intro w hw
  have h := KernelMiscCoset.C7262.matCheck_centWords
  rw [matCheck, List.all_eq_true] at h
  exact lift_genSz_eq_one (wordMat_eq_one (of_decide_eq_true (h w hw)))

theorem two_dvd_orderOf_invWords : ∀ u, (u, 2) ∈ invWords →
    2 ∣ orderOf (PresentedGroup.mk (wordSet (coverWords rels wWord)) (FreeGroup.mk u)) := by
  have hpt := Act.coverPointOK_sound rels wWord ([] : List (List (Fin 2 × Bool)))
    KernelSz8.hR KernelSz8.hW (Act.coverPointOK_of_allR CFSG.KAct.XSz8H.all)
  intro u hu
  have h := CFSG.KAct.XSz8H.Inv7262.invCyc
  rw [List.all_eq_true] at h
  have hc : Act.cycleOK CFSG.KAct.XSz8H.A (Nat.add 2 2) (u.map letterCode) 2 = true :=
    h (u, 2) hu
  have := Act.cycleOK_sound (coverWords rels wWord ++ []) rfl (by norm_num) hpt u hc
  rw [List.append_nil] at this
  exact this

end CertificateChecks.Batch7262

namespace Certificates

open CertificateChecks

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8 CFSG.CosetTable CFSG.KC.MiscCoset
  CFSG.Certificates.CosetEnumeration

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8 CFSG.CosetTable in
theorem certificate7262 :
    (∀ w ∈ centWords, FreeGroup.lift genSz (FreeGroup.mk w) = 1)
    ∧ ∀ u, (u, 2) ∈ invWords →
      2 ∣ orderOf (PresentedGroup.mk (wordSet (coverWords rels CFSG.LieType.Multipliers.Sz8.wWord)) (FreeGroup.mk u)) :=
  ⟨CertificateChecks.Batch7262.lift_genSz_centWords, CertificateChecks.Batch7262.two_dvd_orderOf_invWords⟩

end Certificates
