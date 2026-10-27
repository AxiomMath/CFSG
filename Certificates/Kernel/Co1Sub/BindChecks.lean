module

public import Certificates.Kernel.Co1Sub.Data
public import Certificates.Data.Kernel.Co1Sub.Txt
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.CFSGNative.Co1Sub.Check
public import CFSG.Certificates.Kernel.Common.StrChars
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

#ks_chars_of CFSG.KD.Co1Sub.AuxT CFSG.Sporadic.Co1Sub.Native.auxText

#ks_chars_of CFSG.KD.Co1Sub.SeedA CFSG.Sporadic.Co1.Native.seedA

#ks_chars_of CFSG.KD.Co1Sub.SeedB CFSG.Sporadic.Co1.Native.seedB

namespace CFSG.KD.Co1Sub

open CFSG.KC.Co1Sub CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.G13 CFSG.KLie.CT

theorem ch120801_txt : andB (charsEq AuxT.chars (wordsC aW))
    (andB (nonemptyK aW) (Nat.beq (lenL aM) 301)) = true := by quickRfl

theorem ch120801_seed : andB (Nat.beq (lenL G) 2)
    (andB (m1Bind SeedA.chars 24 (getL 0 G 0)) (m1Bind SeedB.chars 24 (getL 0 G 1))) = true := by
  quickRfl

end CFSG.KD.Co1Sub

end
