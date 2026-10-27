module

public import CFSG.LieType.Multipliers.U43Data
import Certificates.Kernel.Multipliers.U43BFacts
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43 Matrix
  CFSG.Assembly.LowTwoRank CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native CFSG.CosetTable in
theorem certificate10012 :
    (rawChainOK 820 (chainS.extract 0 2) chainS
      (CFSG.LieType.Multipliers.U43.chainBase.map Fin.val).toArray chainW 4 = true)
    ∧ ((rawOrbitSizes 820 chainS
      (CFSG.LieType.Multipliers.U43.chainBase.map Fin.val).toArray).prod = 3265920)
    ∧ (∀ v ∈ checkWords, wordProd (img2 (permOfArr 820 tabA) (permOfArr 820 tabB)) v = 1)
    ∧ (Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 3265920) :=
  ⟨KernelU43B.chain_check, KernelU43B.chain_orbits, KernelU43B.checkWords_eval, KernelU43B.card_le⟩

end Certificates
