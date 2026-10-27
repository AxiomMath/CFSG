module

public import CFSG.RankThree.PartTwo.KFacts.KS166J2A5CheckInputs
import Certificates.Kernel.Misc.Perm.J2KS166
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.ArrEnumOps

public section

namespace CertificateChecks.KernelMisc.J2Fam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Mathieu
open CFSG.Monster.B.Co2 (allLt_iff)
open CertificateChecks.KernelMisc.J2C3 (hw cz czp pX hI pI)

theorem ks166 : CFSG.RankThree.PartTwo.KFacts.KS166.ks166InvCheck = true := by
  unfold CFSG.RankThree.PartTwo.KFacts.KS166.ks166InvCheck
  rw [allLt_iff, cz.1]
  intro k hk
  have hp := czp k hk
  have hxt := permB_pcomp hw pX hp
  have h := ksCz_All k hk
  dsimp only
  unfold CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.isInvolA CFSG.ComponentClassification.J2Cover.commA
  rw [cz.2.1 k hk, J2C3.hx, hv1, hv2, ← hI, comp_unpack hw hp hp, comp_unpack hw pX hp,
    pow_unpack hw hxt, comp_unpack hw hp pV1, comp_unpack hw pV1 hp, comp_unpack hw hp pV2,
    comp_unpack hw pV2 hp, eqA_unpack hw (permB_pcomp hw hp hp) pI, eqA_unpack hw hp pI,
    eqA_unpack hw (permB_ppow hw hxt 5) pI, eqA_unpack hw (permB_pcomp hw hp pV1)
      (permB_pcomp hw pV1 hp),
    eqA_unpack hw (permB_pcomp hw hp pV2) (permB_pcomp hw pV2 hp)]
  exact h

end CertificateChecks.KernelMisc.J2Fam

namespace Certificates

open CertificateChecks

theorem certificate919242 : CFSG.RankThree.PartTwo.KFacts.KS166.ks166InvCheck = true := KernelMisc.J2Fam.ks166

end Certificates
