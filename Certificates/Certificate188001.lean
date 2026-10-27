module

public import Certificates.Data.HuppertU38.Data
public import CFSG.RankThree.PartOne.KS.PKit
import Certificates.Kernel.SchreierFam.C188001F

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Mathieu in
theorem certificate188001 :
    (rawChainOK 513 (strong1.extract 0 9) strong1 base1 words1 1 = true ∧
      rawOrbitSizes 513 strong1 base1 = [513, 512, 378]) ∧
    (rawChainOK 513 (strong2.extract 0 9) strong2 base2 words2 1 = true) ∧
    (validA 513 x19 = true ∧ siftA 513 (rawLevels 513 strong1 base1) base1 0 x19 = true ∧
      eqA 513 (powArr 513 x19 19) (CFSG.Monster.B.Co2.Native.idA 513) = true ∧ eqA 513 (powArr 513 x19 1) (CFSG.Monster.B.Co2.Native.idA 513) = false ∧
      centOKP 19 513 strong1 base1 x19 rels1 gens1 ps1 cert1 57 = true) ∧
    (validA 513 sigma0 = true ∧ siftA 513 (rawLevels 513 strong2 base2) base2 0 sigma0 = true ∧
      eqA 513 (powArr 513 sigma0 2) (CFSG.Monster.B.Co2.Native.idA 513) = true ∧ eqA 513 (powArr 513 sigma0 1) (CFSG.Monster.B.Co2.Native.idA 513) = false ∧
      sigma0[base2[0]!]! = base2[0]! ∧ sigma0[base2[1]!]! = base2[1]! ∧ base2[0]! ≠ base2[1]! ∧
      centOKP 2 513 strong2 base2 sigma0 rels2 gens2 ps2 cert2 3024 = true ∧
      eqA 513 (powArr 513 gens2[0]! 9) (CFSG.Monster.B.Co2.Native.idA 513) = true ∧
      eqA 513 (powArr 513 gens2[0]! 3) (CFSG.Monster.B.Co2.Native.idA 513) = false) ∧
    (validA 513 y9 = true ∧ siftA 513 (rawLevels 513 strong1 base1) base1 0 y9 = true ∧
      eqA 513 (powArr 513 y9 9) (CFSG.Monster.B.Co2.Native.idA 513) = true ∧ eqA 513 (powArr 513 y9 3) (CFSG.Monster.B.Co2.Native.idA 513) = false ∧
      y9[base1[0]!]! = base1[0]!) ∧
    (validA 513 x7 = true ∧ siftA 513 (rawLevels 513 strong1 base1) base1 0 x7 = true ∧
      eqA 513 (powArr 513 x7 7) (CFSG.Monster.B.Co2.Native.idA 513) = true ∧ eqA 513 (powArr 513 x7 1) (CFSG.Monster.B.Co2.Native.idA 513) = false ∧
      ((List.range 513).filter fun p => x7[p]! == p).length = 2) := KernelSchreierFam.U38B.facts

end Certificates
