module

public import Certificates.Kernel.BabyMonster.CTIB.LiftBase

public section

namespace CertificateChecks.KernelBM.CTIB

open CFSG.Monster.B.CTIB.Native CFSG.KC.BM

theorem h10c0 : ((((liftWord10.drop 1).take 8).foldl stepA (genImgs 1)).toList ==
    dec23 CTIBSmall.X2) = true := by quickRfl

theorem h10c1 : ((((liftWord10.drop 9).take 8).foldl stepA (decA CTIBSmall.X2)).toList ==
    dec23 CTIBSmall.X3) = true := by quickRfl

theorem h10c2 : ((((liftWord10.drop 17).take 8).foldl stepA (decA CTIBSmall.X3)).toList ==
    dec23 CTIBSmall.X4) = true := by quickRfl

theorem h10c3 : ((((liftWord10.drop 25).take 8).foldl stepA (decA CTIBSmall.X4)).toList ==
    dec23 CTIBSmall.X5) = true := by quickRfl

theorem h10c4 : ((((liftWord10.drop 33).take 8).foldl stepA (decA CTIBSmall.X5)).toList ==
    dec23 CTIBSmall.X6) = true := by quickRfl

theorem h10c5 : ((((liftWord10.drop 41).take 8).foldl stepA (decA CTIBSmall.X6)).toList ==
    dec23 CTIBSmall.X7) = true := by quickRfl

theorem h10c6 : ((((liftWord10.drop 49).take 8).foldl stepA (decA CTIBSmall.X7)).toList ==
    dec23 CTIBSmall.X8) = true := by quickRfl

theorem h10c7 : ((((liftWord10.drop 57).take 8).foldl stepA (decA CTIBSmall.X8)).toList ==
    dec23 CTIBSmall.X9) = true := by quickRfl

end CertificateChecks.KernelBM.CTIB

end
