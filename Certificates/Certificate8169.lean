module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Base
import Certificates.Kernel.Misc.Perm.J2Elts45
import Certificates.Kernel.Misc.Perm.J2EnumLoc
import Certificates.Kernel.Misc.Perm.J2EnumE0
import Certificates.Kernel.Misc.Perm.J2CentGJ

public section

namespace Certificates

open CertificateChecks.KernelMisc

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec4.Sporadic CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
  CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 in
theorem certificate8169 :
    (chkElts45 = true ∧ chkEnum45 = true ∧ chkLocal45 = true ∧ chkW = true ∧ chkS = true ∧
      chkE0 = true ∧ chkVk = true) ∧
    (∀ g : GJ, Rep 315 xArr g.1 → Subgroup.centralizer ({g} : Set GJ) = subOf gensCaArr) ∧
    (∀ g : GJ, Rep 315 v1Arr g.1 → Subgroup.centralizer ({g} : Set GJ) = subOf gensCvArr) :=
  ⟨⟨J2En.chkElts45_true, J2En.chkEnum45_true, J2En.chkLocal45_true, J2En.chkW_true,
      J2En.chkS_true, J2En.chkE0_true, J2En.chkVk_true⟩,
    fun _ hg => J2Cent.centralizer_x_eq hg, fun _ hg => J2Cent.centralizer_v1_eq hg⟩

end Certificates
