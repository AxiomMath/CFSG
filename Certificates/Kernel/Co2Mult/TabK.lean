module

public import Certificates.Data.Kernel.TabMat
public import Certificates.Kernel.VecCert.Co2
public import Certificates.Kernel.Co2Mult.Pairs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CertificateChecks.KernelCo2Mult

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.VecK CFSG.KC.TabMat CertificateChecks.KernelVec.Co2
  CFSG.Sporadic.Co2.Native CFSG.Sporadic.Recognition.Co2Multiplier
  CFSG.Sporadic.Recognition.CoverRecipe

theorem hseed :
    seedK csA csB (co2Data ()).d MA MB NA NB (co2Data ()).expA (co2Data ()).expB = true := by
  quickRfl

theorem hn :
    andB (Nat.blt (nat_lit 0) (co2Data ()).n) (Nat.blt (co2Data ()).n (pw2 (nat_lit 30))) = true := by
  quickRfl

theorem hP0 : Nat.beq (lk Pt (nat_lit 32) (nat_lit 0)) (co2Data ()).v0 = true := by quickRfl

theorem hAi : Nat.beq (mulF (co2Data ()).d NA NAi) (idF (co2Data ()).d) = true := by quickRfl

theorem hBi : Nat.beq (mulF (co2Data ()).d NB NBi) (idF (co2Data ()).d) = true := by quickRfl

theorem tabK : tabMatK (co2Data ()).d NA NAi NB NBi (co2GenWords.map natWord)
    (co2Pairs.map fun q => (natWord q.1, natWord q.2)) = true := by
  quickRfl

end CertificateChecks.KernelCo2Mult

end
