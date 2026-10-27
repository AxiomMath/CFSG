module

public import CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.Sporadic.Schreier.TitsArrays
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
import Certificates.Kernel.TitsW.Alg
import Certificates.Kernel.TitsW.C7660
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelTitsW

namespace Certificates

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits in
theorem certificate7660 :
    ([([13], [2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, -4, 3, 3, -4, -4]),
        ([-4, -4], [-4, 3, 3, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1])] :
        List (List ℤ × List ℤ)).all (fun c =>
      let g := wordArr 1755 titsDerivedArrs c.2
      let h := compA 1755 (invCand 1755 g) (wordArr 1755 titsDerivedArrs c.1)
      isInvA 1755 g (invCand 1755 g) && eqA 1755 (compA 1755 g (compA 1755 g g)) (idA 1755) &&
        eqA 1755 (compA 1755 h (compA 1755 h h)) (idA 1755)) = true ∧
    (let g := wordArr 1755 titsDerivedArrs [13, 13, 4]
     let h := compA 1755 (invCand 1755 g) (wordArr 1755 titsDerivedArrs [-4, 3, 3])
     isInvA 1755 g (invCand 1755 g) &&
       eqA 1755 (compA 1755 g (compA 1755 g (compA 1755 g (compA 1755 g g)))) (idA 1755) &&
       eqA 1755 (compA 1755 h (compA 1755 h (compA 1755 h (compA 1755 h h)))) (idA 1755)) = true := by
  have l1 : CFSG.KS.Raw.lettersK 13 [2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, -4, 3, 3, -4, -4] = true := by
    quickRfl
  have l2 : CFSG.KS.Raw.lettersK 13 [13] = true := by quickRfl
  have l3 : CFSG.KS.Raw.lettersK 13 [-4, 3, 3, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1] = true := by
    quickRfl
  have l4 : CFSG.KS.Raw.lettersK 13 [-4, -4] = true := by quickRfl
  have l5 : CFSG.KS.Raw.lettersK 13 [13, 13, 4] = true := by quickRfl
  have l6 : CFSG.KS.Raw.lettersK 13 [-4, 3, 3] = true := by quickRfl
  simp (maxDischargeDepth := 64) only [List.all_cons, List.all_nil, Bool.and_true,
    wordArr_D l1, wordArr_D l2, wordArr_D l3, wordArr_D l4, wordArr_D l5, wordArr_D l6,
    invCand_G, compA_G, eqA_G, isInvA_G, idA_G, Gd.mul, Gd.inv, Gd.one, Gd_WD,
    C7660.g1, C7660.h1, C7660.g2, C7660.h2, C7660.g3, C7660.h3, Bool.true_and, and_self]

end Certificates
