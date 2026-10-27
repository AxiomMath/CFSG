
module


public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public import Certificates.Data.CFSGNative.J2.Certificate
import Certificates.Kernel.J2Cover.K19
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native in
theorem certificate10019 :
    (rawChainOK 315 (autStrong.extract 0 2) autStrong autBase autWords 4 = true ∧
      rawOrbitSizes 315 autStrong autBase = [315, 160, 12])
    ∧ (allLt 315 (fun i => ap (CFSG.Sporadic.J2.Native.orbitData ()).alpha i == (autStrong[0]!)[i]! &&
      ap (CFSG.Sporadic.J2.Native.orbitData ()).beta i == (autStrong[1]!)[i]!) = true)
    ∧ (ordTest 315 2 CFSG.ComponentClassification.J2Cover.tblA = true ∧ ordTest 315 3 CFSG.ComponentClassification.J2Cover.tblB = true ∧
      pairTest 315 7 12 2 3 CFSG.ComponentClassification.J2Cover.tblA CFSG.ComponentClassification.J2Cover.tblB = true ∧
      (orderTablesOf (CFSG.Sporadic.Th.Native.idT 315) 2).length = 2835 ∧ (orderTablesOf (CFSG.Sporadic.Th.Native.idT 315) 3).length = 17360 ∧
      CFSG.Sporadic.Schreier.Native.classOK 315 #[CFSG.ComponentClassification.J2Cover.tblA, CFSG.ComponentClassification.J2Cover.tblB] #[tblAInv, tblBInv] (orderTablesOf (CFSG.Sporadic.Th.Native.idT 315) 2) 4000 = true ∧
      classTotal 315 #[CFSG.ComponentClassification.J2Cover.tblA, CFSG.ComponentClassification.J2Cover.tblB] #[tblAInv, tblBInv] (orderTablesOf (CFSG.Sporadic.Th.Native.idT 315) 2)
        (orderTablesOf (CFSG.Sporadic.Th.Native.idT 315) 3) 4000 7 12 2 3 = 1209600)
    ∧ (inP outerArr = false ∧ inP (compA 315 outerArr (compA 315 autStrong[0]! outerArr)) = true ∧
      inP (compA 315 outerArr (compA 315 autStrong[1]! outerArr)) = true)
    ∧ (inP twoAArr = true ∧
      CFSG.Sporadic.Schreier.Native.repsOK 315 #[CFSG.ComponentClassification.J2Cover.tblA, CFSG.ComponentClassification.J2Cover.tblB] #[tblAInv, tblBInv] (orderTablesOf (CFSG.Sporadic.Th.Native.idT 315) 2) [CFSG.ComponentClassification.J2Cover.tblA, tblTwoA]
        4000 = true ∧
      repSizes 315 #[CFSG.ComponentClassification.J2Cover.tblA, CFSG.ComponentClassification.J2Cover.tblB] #[tblAInv, tblBInv] [CFSG.ComponentClassification.J2Cover.tblA, tblTwoA] 4000 = [2520, 315] ∧
      CFSG.Sporadic.Schreier.Native.repsOK 315 #[CFSG.ComponentClassification.J2Cover.tblA, CFSG.ComponentClassification.J2Cover.tblB] #[tblAInv, tblBInv] (orderTablesOf tblU 2) [tblU] 4000 = true ∧
      repSizes 315 #[CFSG.ComponentClassification.J2Cover.tblA, CFSG.ComponentClassification.J2Cover.tblB] #[tblAInv, tblBInv] [tblU] 4000 = [1800])
    ∧ (rawChainOK 315 (cent2BStrong.extract 0 2) cent2BStrong cent2BBase cent2BWords 4 = true ∧
      rawOrbitSizes 315 cent2BStrong cent2BBase = [60, 4] ∧
      inP cent2BStrong[0]! = true ∧ inP cent2BStrong[1]! = true ∧
      CFSG.ComponentClassification.J2Cover.commA cent2BStrong[0]! autStrong[0]! = true ∧ CFSG.ComponentClassification.J2Cover.commA cent2BStrong[1]! autStrong[0]! = true ∧
      oddWitnessOK 315 15
        (filterProducts 315 allTrue (chainTables 315 cent2BStrong cent2BBase) (CFSG.Sporadic.Th.Native.idT 315) []) =
        true)
    ∧ (rawChainOK 315 (cent2AStrong.extract 0 2) cent2AStrong cent2ABase cent2AWords 4 = true ∧
      rawOrbitSizes 315 cent2AStrong cent2ABase = [160, 4, 3] ∧
      inP cent2AStrong[0]! = true ∧ inP cent2AStrong[1]! = true ∧
      CFSG.ComponentClassification.J2Cover.commA cent2AStrong[0]! twoAArr = true ∧ CFSG.ComponentClassification.J2Cover.commA cent2AStrong[1]! twoAArr = true ∧
      oddWitnessOK 315 15
        (filterProducts 315 allTrue (chainTables 315 cent2AStrong cent2ABase) (CFSG.Sporadic.Th.Native.idT 315) []) =
        true)
    ∧ (rawChainOK 315 (centOuterStrong.extract 0 2) centOuterStrong centOuterBase centOuterWords 4 =
        true ∧
      rawOrbitSizes 315 centOuterStrong centOuterBase = [42, 8] ∧
      inP centOuterStrong[0]! = true ∧ inP centOuterStrong[1]! = true ∧
      CFSG.ComponentClassification.J2Cover.commA centOuterStrong[0]! outerArr = true ∧ CFSG.ComponentClassification.J2Cover.commA centOuterStrong[1]! outerArr = true ∧
      oddWitnessOK 315 21
        (filterProducts 315 allTrue (chainTables 315 centOuterStrong centOuterBase) (CFSG.Sporadic.Th.Native.idT 315) []) =
        true)
    ∧ (rawChainOK 315 (sylowStrong.extract 0 3) sylowStrong sylowBase CFSG.ComponentClassification.J2Cover.sylowWords 4 = true ∧
      rawOrbitSizes 315 sylowStrong sylowBase = [64, 4] ∧
      inP (compA 315 sylowStrong[0]! outerArr) = true ∧
      inP (compA 315 sylowStrong[1]! outerArr) = true ∧
      inP (compA 315 sylowStrong[2]! outerArr) = true) :=
  KernelJ2Cover.facts10019

end Certificates
