module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TInputs
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
import Certificates.Kernel.SporSch.Tits.T614

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native in
open CFSG.Monster.B.Co2.Native CFSG.Quasithin.H13.Tits614 in
theorem certificate7195 :
    (CFSG.Monster.B.Co2.Native.allLt 1755 (fun x => decide (x < 3) ||
        !(CFSG.Monster.B.Co2.Native.allLt 3 fun j => (titsRArrs[j]!)[x]! == x)) = true)
    ∧ (lettersOK 3 pWord = true ∧ eqA 1755 (pow5Arr CFSG.Quasithin.H13.Tits614.pArr) (idA 1755) = true)
    ∧ ((∀ i < 5, lettersOK 4 (eXWord i) = true ∧ lettersOK 4 (eYWord i) = true) ∧
      eqA 1755 (eProdArr 0) (idA 1755) = true ∧ (CFSG.Monster.B.Co2.Native.allLt 5 fun i => inE (eGenArr i)) = true ∧
      (CFSG.Monster.B.Co2.Native.allLt 32 fun v => CFSG.Monster.B.Co2.Native.allLt 32 fun w => inE (compA 1755 (eProdArr v) (eProdArr w)) &&
        eqA 1755 (compA 1755 (eProdArr v) (eProdArr w))
          (compA 1755 (eProdArr w) (eProdArr v))) = true ∧
      (CFSG.Monster.B.Co2.Native.allLt 32 fun v => eqA 1755 (compA 1755 (eProdArr v) (eProdArr v)) (idA 1755)) = true ∧
      eArrs.Pairwise (fun a b => eqA 1755 a b = false) ∧
      eArrs.all (fun c => isInvA 1755 c (invCand 1755 c)) = true ∧
      (CFSG.Monster.B.Co2.Native.allLt 32 fun v => inJ (eProdArr v) && CFSG.Sporadic.Schreier.Tits.inK (eProdArr v)) = true ∧
      (CFSG.Monster.B.Co2.Native.allLt 5 fun i => inE (CFSG.Sporadic.Schreier.Tits.conjArr CFSG.Quasithin.H13.Tits614.pArr (eGenArr i))) = true ∧ inE titsZArr = true)
    ∧ (all5 1755 titsSLevels (fun a => !(inJ a) ||
        !(eqA 1755 (compA 1755 a CFSG.Quasithin.H13.Tits614.pArr) (compA 1755 CFSG.Quasithin.H13.Tits614.pArr a)) || eqA 1755 a (idA 1755) ||
        eqA 1755 a titsZArr) = true)
    ∧ (all5 1755 titsHLevels (fun a =>
        !(CFSG.Monster.B.Co2.Native.allLt 3 fun i => CFSG.Sporadic.Schreier.Tits.inS (CFSG.Sporadic.Schreier.Tits.conjArr a titsSArrs[i]!)) || CFSG.Sporadic.Schreier.Tits.inS a) = true)
    ∧ (all5 1755 titsSLevels (fun a =>
        !(CFSG.Sporadic.Schreier.Tits.inS (compA 1755 (compA 1755 (invCand 1755 CFSG.Quasithin.H13.Tits614.pArr) a) CFSG.Quasithin.H13.Tits614.pArr)) || inJ a) = true)
    ∧ (all5 1755 titsSLevels (fun a =>
        !(CFSG.Monster.B.Co2.Native.allLt 3 fun i => inE (commArr 1755 (outerArr a) titsHArrs[i]!)) ||
        ((CFSG.Monster.B.Co2.Native.allLt 2 fun j => CFSG.Sporadic.Schreier.Tits.inK (CFSG.Sporadic.Schreier.Tits.conjArr (outerArr a) titsKArrs[j]!)) &&
          (CFSG.Monster.B.Co2.Native.allLt 4 fun j => CFSG.Sporadic.Schreier.Tits.inK (commArr 1755 (outerArr a) titsNArrs[j]!)))) = true) := KernelSporSch.T614.batch7195

end Certificates
