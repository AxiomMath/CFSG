module

public import CFSG.Quasithin.Background.F7TwoInvTitsInputs
import Certificates.Kernel.TitsW.Alg
import Certificates.Kernel.TitsW.C7410
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.F7Two
open CertificateChecks.KernelTitsW

namespace Certificates

open CFSG.Quasithin.F7Two in
theorem certificate7410 : invTitsCheck () = true := by
  have l1 : CFSG.KS.Raw.lettersK 13 titsCenterWord = true := by quickRfl
  have l2 : CFSG.KS.Raw.lettersK 13 invTitsZConjWord = true := by quickRfl
  have l3 : CFSG.KS.Raw.lettersK 13 titsTWord = true := by quickRfl
  have l4 : CFSG.KS.Raw.lettersK 13 invTitsTConjWord = true := by quickRfl
  have o1 : lettersOK 13 titsCenterWord = true := by decide
  have o2 : lettersOK 13 invTitsZConjWord = true := by decide
  have o3 : lettersOK 13 titsTWord = true := by decide
  have o4 : lettersOK 13 invTitsTConjWord = true := by decide
  have hpow : ∀ p, Gd p → ∀ k, invTitsPow (CFSG.KS.Raw.unpack 1755 11 p) k =
      CFSG.KS.Raw.unpack 1755 11 (ppw p k) := fun p hp =>
    pow_G hp (by simp [invTitsPow]) (fun k => by simp [invTitsPow])
  simp (maxDischargeDepth := 64) only [invTitsCheck, invTitsClassCheck, invTitsHasOrder,
    invTitsComm, conjArr, o1, o2, o3, o4, Bool.true_and,
    wordArr_D l1, wordArr_D l2, wordArr_D l3, wordArr_D l4,
    derived_get (show 0 < 13 by norm_num), derived_get (show 1 < 13 by norm_num),
    invCand_G, compA_G, eqA_G, isInvA_G, idA_G, hpow, Gd.mul, Gd.inv, Gd.one, Gd_WD, Gd_DS,
    Gd.pow]
  simp only [titsCenterWord, invTitsZConjWord, titsTWord, invTitsTConjWord,
    C7410.z2, C7410.z0p, C7410.z0n, C7410.z1p, C7410.z1n,
    C7410.t2, C7410.t0p, C7410.t0n, C7410.t1p, C7410.t1n, Bool.and_self]

end Certificates
