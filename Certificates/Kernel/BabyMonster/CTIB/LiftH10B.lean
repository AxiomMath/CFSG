module

public import Certificates.Kernel.BabyMonster.CTIB.LiftBase

public section

namespace CertificateChecks.KernelBM.CTIB

open CFSG.Monster.B.CTIB.Native CFSG.KC.BM

theorem h10c8 : ((((liftWord10.drop 65).take 8).foldl stepA (decA CTIBSmall.X9)).toList ==
    dec23 CTIBSmall.X10) = true := by quickRfl

theorem h10c9 : ((((liftWord10.drop 73).take 8).foldl stepA (decA CTIBSmall.X10)).toList ==
    dec23 CTIBSmall.X11) = true := by quickRfl

theorem h10c10 : ((((liftWord10.drop 81).take 8).foldl stepA (decA CTIBSmall.X11)).toList ==
    dec23 CTIBSmall.X12) = true := by quickRfl

theorem h10c11 : ((((liftWord10.drop 89).take 8).foldl stepA (decA CTIBSmall.X12)).toList ==
    dec23 CTIBSmall.X13) = true := by quickRfl

theorem h10c12 : ((((liftWord10.drop 97).take 8).foldl stepA (decA CTIBSmall.X13)).toList ==
    dec23 CTIBSmall.X14) = true := by quickRfl

theorem h10c13 : ((((liftWord10.drop 105).take 8).foldl stepA (decA CTIBSmall.X14)).toList ==
    dec23 CTIBSmall.X15) = true := by quickRfl

theorem h10c14 : ((((liftWord10.drop 113).take 8).foldl stepA (decA CTIBSmall.X15)).toList ==
    dec23 CTIBSmall.X16) = true := by quickRfl

theorem h10c15 : ((((liftWord10.drop 121).take 8).foldl stepA (decA CTIBSmall.X16)).toList ==
    dec23 CTIBSmall.X17) = true := by quickRfl

theorem h10c16 : ((((liftWord10.drop 129).take 8).foldl stepA (decA CTIBSmall.X17)).toList ==
    dec23 CTIBSmall.X18) = true := by quickRfl

end CertificateChecks.KernelBM.CTIB

end
