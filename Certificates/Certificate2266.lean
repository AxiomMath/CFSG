module

public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
import Certificates.Kernel.SporSch.Tits.Inv2266

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSporSch.TitsInv in
open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native in
open CFSG.Monster.B.Co2.Native in
theorem certificate2266 : (lettersOK 13 titsTWord = true ∧ inK titsTArr = true ∧
      eqA 1755 titsTArr (idA 1755) = false ∧
      eqA 1755 (compA 1755 titsTArr titsTArr) (idA 1755) = true ∧
      (∀ j < 3, inS (conjArr titsGenArrs[1]! titsSArrs[j]!) = true) ∧
      inS (compA 1755 titsGenArrs[1]! titsGenArrs[1]!) = true ∧ inS titsGenArrs[1]! = false ∧
      all5 1755 titsSLevels (fun a =>
        !eqA 1755 (compA 1755 (compA 1755 a titsGenArrs[1]!) (compA 1755 a titsGenArrs[1]!))
          (idA 1755)) = true
    )
    ∧ (titsInvCert.all (fun bw => lettersOK 13 bw.2 &&
        isInvA 1755 (wordArr 1755 titsDerivedArrs bw.2)
          (invCand 1755 (wordArr 1755 titsDerivedArrs bw.2))) = true ∧
      all5 1755 titsSLevels (fun a => !eqA 1755 (compA 1755 a a) (idA 1755) ||
        eqA 1755 a (idA 1755) || anyEq titsInvConj a) = true
    )
    ∧ ((∀ p < 1755, titsTArr[p]! = p → p ∈ titsFixWords.map Prod.fst) ∧
      titsFixWords.all (fun pw => lettersOK 13 pw.2 &&
        (wordArr 1755 titsDerivedArrs pw.2)[0]! == pw.1 &&
        isInvA 1755 (wordArr 1755 titsDerivedArrs pw.2)
          (invCand 1755 (wordArr 1755 titsDerivedArrs pw.2))) = true ∧
      all5 1755 titsHLevels (fun a => isInvA 1755 a (invCand 1755 a) &&
        titsExcl.all fun y => !eqA 1755 (conjArr a titsTArr) y) = true ∧
      all5 1755 titsHLevels (fun a => !commA a titsTArr || anyEq titsCHt a) = true ∧
      titsCHt.length = 512 ∧
      titsCHt.all (fun c => isInvA 1755 c (invCand 1755 c) && commA c titsTArr && inH c) = true ∧
      titsCHt.Pairwise (fun a b => eqA 1755 a b = false)
    )
    ∧ (all5 1755 titsNLevels (fun a => !commA a titsTArr || anyEq titsCNt a) = true ∧
      titsCNt.length = 1536 ∧ titsQt.length = 256 ∧ titsCCQ.length = 8 ∧
      titsCNt.all (fun c => isInvA 1755 c (invCand 1755 c) && commA c titsTArr && inN c) = true ∧
      titsCNt.Pairwise (fun a b => eqA 1755 a b = false) ∧ titsCCQ.all inK = true
    ) :=
  ⟨part1, part2, ⟨part3a.1, part3a.2.1, part3a.2.2, part3b⟩, part4⟩

end Certificates
