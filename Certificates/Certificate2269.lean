module

public import CFSG.Sporadic.Schreier.TitsPrimCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsLocal
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Sporadic.Schreier.TitsStabCheck
public meta import CFSG.Certificates.NativeInvariantMerge
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
import Certificates.Kernel.SporSch.Tits.Prim2269

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Tits CFSG.Certificates in
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate2269 : titsH0Idx = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] ∧
    titsStabReps = [1, 6, 24, 87] ∧ titsStabSizes = [1, 10, 80, 640, 1024] ∧
    orbitLabelOK 1755 titsH0Arrs 5 titsH0Forest.1 #[0, 1, 6, 24, 87] titsH0Forest.2.1
      titsH0Forest.2.2.1 titsH0Forest.2.2.2 = true ∧
    (List.range 5).map (labelCount 1755 titsH0Forest.1) = titsStabSizes ∧
    CFSG.Monster.B.Co2.Native.allLt 1755 (fun x => decide ((#[0, 1, 6, 24, 87] : Array ℕ)[titsH0Forest.1[x]!]! ≤ x)) =
      true ∧
    (∀ l < 4, (titsOrigMerge l).length = 1753 ∧
      mergeOK 1755 titsDArrs 0 titsStabReps[l]! (mergeVals (titsOrigMerge l)) = true) ∧
    titsOtherReps = [0, 1, 7, 27, 107, 141] ∧ titsOtherSizes = [1, 12, 96, 768, 1024, 1024] ∧
    orbitLabelOK 2925 titsNStarArrs 6 titsNForest.1 #[0, 1, 7, 27, 107, 141] titsNForest.2.1
      titsNForest.2.2.1 titsNForest.2.2.2 = true ∧
    (List.range 6).map (labelCount 2925 titsNForest.1) = titsOtherSizes ∧
    CFSG.Monster.B.Co2.Native.allLt 2925 (fun x => decide ((#[0, 1, 7, 27, 107, 141] : Array ℕ)[titsNForest.1[x]!]! ≤ x)) =
      true ∧
    (∀ l < 5, (titsOtherMerge l).length = 2923 ∧
      mergeOK 2925 titsDStarArrs 0 titsOtherReps[l + 1]! (mergeVals (titsOtherMerge l)) =
        true) := KernelSporSch.TitsPrim.facts

end Certificates
