module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFibreFact
public import Certificates.Certificate136200
public import Certificates.Kernel.M3BFib.Fib13Roots

public section

namespace Certificates

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF in
theorem certificate136204 :     FibreRoots 1 := by
  intros
  exact CFSG.KC.M3BF.m3bf_roots1 (Certificates.certificate136200)

end Certificates
