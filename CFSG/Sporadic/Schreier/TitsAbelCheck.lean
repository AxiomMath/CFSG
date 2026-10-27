module

public import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Sporadic.Schreier.TitsAbelCheckInputs
public import Certificates.Certificate2261

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem titsAbel_check :
    titsSWords.length = 3 ∧ titsRWords.length = 3 ∧ titsProvenance.length = 3 ∧
    (∀ k < 3, titsRWords[k]! = provWord titsSWords[titsProvenance[k]!.1]!
      titsSWords[titsProvenance[k]!.2.1]! titsProvenance[k]!.2.2 ∧
      titsProvenance[k]!.1 < 3 ∧ titsProvenance[k]!.2.1 < 3 ∧
      lettersOK 13 titsProvenance[k]!.2.2 = true ∧
      isInvA 1755 (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2)
        (invCand 1755 (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2)) = true ∧
      inS (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2) = true ∧
      eqA 1755 titsRArrs[k]! (compA 1755 (compA 1755
        (invCand 1755 (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2))
        (commArr 1755 titsSArrs[titsProvenance[k]!.1]! titsSArrs[titsProvenance[k]!.2.1]!))
        (wordArr 1755 titsDerivedArrs titsProvenance[k]!.2.2)) = true) ∧
    (∀ s < 3, ∀ r < 3, inR (compA 1755 (compA 1755 titsSArrs[s]! titsRArrs[r]!)
      (invCand 1755 titsSArrs[s]!)) = true) ∧
    (∀ a < 3, ∀ b < 3, inR (commArr 1755 titsSArrs[a]! titsSArrs[b]!) = true) :=
  Certificates.certificate2261.1

theorem titsAbel_check2 :
    isInvA 1755 titsXArr (invCand 1755 titsXArr) = true ∧
    isInvA 1755 titsYArr (invCand 1755 titsYArr) = true ∧
    inS titsXArr = true ∧ inS titsYArr = true ∧
    inR (titsXYArr 4 0) = true ∧ inR (titsXYArr 0 2) = true ∧
    (∀ i < 4, ∀ j < 2, isInvA 1755 (titsXYArr i j) (invCand 1755 (titsXYArr i j)) = true) :=
  Certificates.certificate2261.2.1

theorem titsAbel_check3 :
    (∀ i < 4, ∀ j < 2, ∀ i' < 4, ∀ j' < 2, (i, j) = (i', j') ∨
      inR (compA 1755 (invCand 1755 (titsXYArr i j)) (titsXYArr i' j')) = false) :=
  Certificates.certificate2261.2.2

end CFSG.Sporadic.Schreier.Tits
