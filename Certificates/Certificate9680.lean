module

public import CFSG.Sporadic.Schreier.RuCheckCentersInputs
public meta import CFSG.Sporadic.Schreier.RuCheckSylow
import Certificates.Kernel.SporSch.Ru.C9680
import Certificates.Kernel.SporSch.Ru.C2248P

public section

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.KC.BfsPin CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuB1K CertificateChecks.KernelSporSch.RuLines
  CertificateChecks.KernelSporSch.Rows2 CertificateChecks.KernelSporSch.RuCt

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate9680 : all2 1920 ruJLevels (fun g => !(allLt 6 fun j => ruComm1920 g (ruJF j)) ||
      eqA 1920 g (idA 1920) || eqA 1920 g (ruEF 0)) = true := by
  refine all2_of_rows_imp RuSF.bindsJ RuSF.pJ RuJS2.hl (Nat.le_refl 2) (fun G hG h => ?_)
    (fun a ha => ZJ.all a (lt_of_lt_of_eq ha (Nat.eq_of_beq_eq_true cJ0)))
  have hA : (allLt 6 fun j => ruComm1920 (unpack 1920 11 G) (ruJF j)) =
      allN 6 (fun j => cm G (RuT1920.L (Nat.add 24 j))) :=
    allLt_eq_allN fun j hj => by
      rw [jf_eq (by omega)]
      exact comm_eq hG (cLj (by omega))
  unfold zjpK at h
  rw [hA]
  cases hc : allN 6 (fun j => cm G (RuT1920.L (Nat.add 24 j)))
  · rfl
  · rw [hc] at h
    have h' : bIf(Nat.beq G (pidn 1920 11), true, Nat.beq G (RF 0)) = true := h
    rw [not_true_or, RuP.idA_eq, eqA1920 hG RuP.cId]
    cases e : Nat.beq G (pidn 1920 11)
    · rw [e] at h'
      have h'' : Nat.beq G (RF 0) = true := h'
      rw [Bool.false_or, ef_eq (by norm_num : 0 < 7), ← Nat.eq_of_beq_eq_true h'']
      exact eqK_sound (Nat.beq_refl G)
    · rfl

end Certificates
