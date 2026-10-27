module

public import Certificates.Kernel.Census.Fi22T2Asm
public import Certificates.Kernel.Census.Fi22T1Asm
public import Certificates.Kernel.Census.Fi22T0Asm
public import Certificates.Kernel.Census.Fi22T2C0
public import Certificates.Kernel.Census.Fi22T1C0
public import Certificates.Kernel.Census.Fi22T0C0
public import Certificates.Kernel.Census.Fi22PkRoots
import Certificates.Kernel.Census.Fi22PkT2R
import Certificates.Kernel.Census.Fi22PkT2A
import Certificates.Kernel.Census.Fi22PkT1R
import Certificates.Kernel.Census.Fi22PkT1A
import Certificates.Kernel.Census.Fi22PkT0R
import Certificates.Kernel.Census.Fi22PkT0A
import Certificates.Data.Kernel.Census.PackedRoot
import Certificates.Data.Kernel.Census.PackedRootBit
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22

theorem fixT2 : Nat.beq (pfix 3510 12 fi22T2Root.x) 694 = true := by quickRfl

theorem fixT1 : Nat.beq (pfix 3510 12 fi22T1Root.x) 182 = true := by quickRfl

theorem fixes : fi22RootsC.map (fun r => pfix 3510 12 r.x) = [694, 182, 54] :=
  beq_iff_eq.1
    (by quickRfl : (fi22RootsC.map (fun r => pfix 3510 12 r.x) == [694, 182, 54]) = true)

theorem lens : fi22RootsC.map (fun r => r.xs.length) = [17, 18, 17] :=
  beq_iff_eq.1 (by quickRfl : (fi22RootsC.map (fun r => r.xs.length) == [17, 18, 17]) = true)

theorem skip1 : pskipFix 3510 12 fi22RootsC 1 = [694] := by
  simp [pskipFix, fi22RootsC, Nat.eq_of_beq_eq_true fixT2]

theorem skip2 : pskipFix 3510 12 fi22RootsC 2 = [694, 182] := by
  simp [pskipFix, fi22RootsC, Nat.eq_of_beq_eq_true fixT2, Nat.eq_of_beq_eq_true fixT1]

theorem rootsII_ok : prootsConjOKB 3510 12 fi22PS inXK inWK false 2 fi22Ks fi22RootsC = true := by
  unfold prootsConjOKB
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨rfl, fun i hi => ?_⟩
  rw [List.mem_range, show fi22RootsC.length = 3 from rfl] at hi
  interval_cases i
  · exact T2.rootII_ok
  · rw [skip1]
    exact T1.rootII_ok
  · rw [skip2]
    exact T0.rootII_ok

theorem roots17_ok : prootsConjOKB 3510 12 fi22PS inXK inWK true 1 fi22Ks fi22RootsC = true := by
  unfold prootsConjOKB
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨rfl, fun i hi => ?_⟩
  rw [List.mem_range, show fi22RootsC.length = 3 from rfl] at hi
  interval_cases i
  · exact T2.root17_ok
  · rw [skip1]
    exact T1.root17_ok
  · rw [skip2]
    exact T0.root17_ok

theorem canon_ok : fi22RootsC.all (canonR 3510 12) = true := by
  simp only [fi22RootsC, List.all_cons, List.all_nil, T2.kC, T1.kC, T0.kC, Bool.and_true]

end CertificateChecks.KernelCensus.Fi22K

end
