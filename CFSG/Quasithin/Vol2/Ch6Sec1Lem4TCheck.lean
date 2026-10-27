module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TInputs
public import Certificates.Certificate7195
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public meta import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public meta import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TInputs
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Quasithin.H13.Tits614

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem fix_check :
    allLt 1755 (fun x => decide (x < 3) ||
      !(allLt 3 fun j => (titsRArrs[j]!)[x]! == x)) = true :=
  Certificates.certificate7195.1

theorem p_check :
    lettersOK 3 pWord = true ∧ eqA 1755 (pow5Arr pArr) (idA 1755) = true :=
  Certificates.certificate7195.2.1

theorem e_check :
    (∀ i < 5, lettersOK 4 (eXWord i) = true ∧ lettersOK 4 (eYWord i) = true) ∧
    eqA 1755 (eProdArr 0) (idA 1755) = true ∧ (allLt 5 fun i => inE (eGenArr i)) = true ∧
    (allLt 32 fun v => allLt 32 fun w => inE (compA 1755 (eProdArr v) (eProdArr w)) &&
      eqA 1755 (compA 1755 (eProdArr v) (eProdArr w))
        (compA 1755 (eProdArr w) (eProdArr v))) = true ∧
    (allLt 32 fun v => eqA 1755 (compA 1755 (eProdArr v) (eProdArr v)) (idA 1755)) = true ∧
    eArrs.Pairwise (fun a b => eqA 1755 a b = false) ∧
    eArrs.all (fun c => isInvA 1755 c (invCand 1755 c)) = true ∧
    (allLt 32 fun v => inJ (eProdArr v) && inK (eProdArr v)) = true ∧
    (allLt 5 fun i => inE (conjArr pArr (eGenArr i))) = true ∧ inE titsZArr = true :=
  Certificates.certificate7195.2.2.1

theorem cjp_check :
    all5 1755 titsSLevels (fun a => !(inJ a) ||
      !(eqA 1755 (compA 1755 a pArr) (compA 1755 pArr a)) || eqA 1755 a (idA 1755) ||
      eqA 1755 a titsZArr) = true :=
  Certificates.certificate7195.2.2.2.1

theorem nhs_check :
    all5 1755 titsHLevels (fun a =>
      !(allLt 3 fun i => inS (conjArr a titsSArrs[i]!)) || inS a) = true :=
  Certificates.certificate7195.2.2.2.2.1

theorem ssp_check :
    all5 1755 titsSLevels (fun a =>
      !(inS (compA 1755 (compA 1755 (invCand 1755 pArr) a) pArr)) || inJ a) = true :=
  Certificates.certificate7195.2.2.2.2.2.1

theorem outer_check :
    all5 1755 titsSLevels (fun a =>
      !(allLt 3 fun i => inE (commArr 1755 (outerArr a) titsHArrs[i]!)) ||
      ((allLt 2 fun j => inK (conjArr (outerArr a) titsKArrs[j]!)) &&
        (allLt 4 fun j => inK (commArr 1755 (outerArr a) titsNArrs[j]!)))) = true :=
  Certificates.certificate7195.2.2.2.2.2.2

end CFSG.Quasithin.H13.Tits614
