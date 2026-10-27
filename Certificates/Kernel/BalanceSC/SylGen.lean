module

public import Certificates.Kernel.BalanceSC.SylData
public import Certificates.Data.Kernel.BalanceSC.Sylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataInputs

public section

open CFSG.KC.BalanceSC
open CFSG.KC.Enum (pg pcomp pidn)
open CFSG.KS.Raw (szOK)
open CFSG.OddStandard.Solomon75.AhatData (gensA)

namespace CFSG.KD.BalSC8

theorem sz : szOK 8 4 = true := by decide +kernel

theorem gsize : (gensA 8).size = 3 := by decide +kernel

theorem gen : ((List.range 3).all fun k => (List.range 8).all fun i =>
    Nat.beq (((gensA 8)[k]!)[i]!) (pg 4 15 (getL 0 G k) i)) = true := by
  decide +kernel

theorem sq : ∀ k < 3, pcomp 8 4 15 (getL 0 G k) (getL 0 G k) = pidn 8 4 := by decide +kernel

end CFSG.KD.BalSC8

namespace CFSG.KD.BalSC9

theorem sz : szOK 9 4 = true := by decide +kernel

theorem gsize : (gensA 9).size = 3 := by decide +kernel

theorem gen : ((List.range 3).all fun k => (List.range 9).all fun i =>
    Nat.beq (((gensA 9)[k]!)[i]!) (pg 4 15 (getL 0 G k) i)) = true := by
  decide +kernel

theorem sq : ∀ k < 3, pcomp 9 4 15 (getL 0 G k) (getL 0 G k) = pidn 9 4 := by decide +kernel

end CFSG.KD.BalSC9

namespace CFSG.KD.BalSC10

theorem sz : szOK 10 4 = true := by decide +kernel

theorem gsize : (gensA 10).size = 3 := by decide +kernel

theorem gen : ((List.range 3).all fun k => (List.range 10).all fun i =>
    Nat.beq (((gensA 10)[k]!)[i]!) (pg 4 15 (getL 0 G k) i)) = true := by
  decide +kernel

theorem sq : ∀ k < 3, pcomp 10 4 15 (getL 0 G k) (getL 0 G k) = pidn 10 4 := by decide +kernel

end CFSG.KD.BalSC10

namespace CFSG.KD.BalSC11

theorem sz : szOK 11 4 = true := by decide +kernel

theorem gsize : (gensA 11).size = 3 := by decide +kernel

theorem gen : ((List.range 3).all fun k => (List.range 11).all fun i =>
    Nat.beq (((gensA 11)[k]!)[i]!) (pg 4 15 (getL 0 G k) i)) = true := by
  decide +kernel

theorem sq : ∀ k < 3, pcomp 11 4 15 (getL 0 G k) (getL 0 G k) = pidn 11 4 := by decide +kernel

end CFSG.KD.BalSC11

end
