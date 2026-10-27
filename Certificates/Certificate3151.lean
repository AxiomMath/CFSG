
module


public import CFSG.Monster.B.Fischer.Fi22CoverCheckInputs
import Certificates.Kernel.Sporadic.Fi22.C3151

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate3151 : fi22OuterTPointsNat.Nodup ∧
      (∀ k < 9, ∀ p < 3510, fi22OuterTPointsNat.contains p =
        fi22OuterTPointsNat.contains ((fi22OuterStrong3510 4)[k]!)[p]!) ∧
      (∀ x : Fin 1024 × Fin 32 × Fin 4, x ≠ (0, 0, 0) →
        moves3 fi22TLevels fi22TPointsArr x.1 x.2.1 x.2.2 = true) ∧
      (Finset.univ.filter fun x : Fin 1024 × Fin 32 × Fin 4 =>
        isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true).card = 3263 ∧
      (∀ x : Fin 1024 × Fin 32 × Fin 4, isInv3 fi22TLevels 3510 x.1 x.2.1 x.2.2 = true →
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).1 < 54 ∧
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.1 < 1024 ∧
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.1 < 32 ∧
        (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.2 < 4 ∧
        conjOK3 fi22TLevels 3510
          (fi22OuterStrong3510 7)[(fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).1]!
          x.1 x.2.1 x.2.2
          (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.1
          (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.1
          (fi22CoverWit[(x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val]!).2.2.2 = true) ∧
      (∀ j < 54, siftA 3510 fi22TLevels #[0, 1, 2, 3, 6, 4] 0 (fi22OuterStrong3510 7)[j]! = true ∧
        eqA 3510 (fi22OuterStrong3510 7)[j]! (idA 3510) = false ∧
        eqA 3510 (compA 3510 (fi22OuterStrong3510 7)[j]! (fi22OuterStrong3510 7)[j]!)
          (idA 3510) = true ∧
        siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
          (fi22OuterStrong3510 8)[j]! = true ∧
        ∃ i < 3, eqA 3510 (compA 3510 (fi22OuterStrong3510 8)[j]! (fi22OuterStrong3510 7)[j]!)
          (compA 3510 (fi22OuterStrong3510 6)[i]! (fi22OuterStrong3510 8)[j]!) = true) ∧
      (∀ i < 3, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
          (fi22OuterStrong3510 6)[i]! = true ∧
        eqA 3510 (fi22OuterStrong3510 6)[i]! (idA 3510) = false ∧
        eqA 3510 (compA 3510 (fi22OuterStrong3510 6)[i]! (fi22OuterStrong3510 6)[i]!)
          (idA 3510) = true) ∧
      (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[0]!)[p.val]! = p.val).card =
        54 ∧
      (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[1]!)[p.val]! = p.val).card =
        182 ∧
      (Finset.univ.filter fun p : Fin 3510 => ((fi22OuterStrong3510 6)[2]!)[p.val]! = p.val).card =
        694 ∧
      eqA 3510 (fi22OuterStrong3510 6)[2]! (fi22OuterStrong3510 1)[0]! = true := KernelSpor.Fi22C3151.certificate3151_of

end Certificates
