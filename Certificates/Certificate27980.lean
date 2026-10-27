module

public import CFSG.HardMathSupport.U4FF.ClassLocCheck
import CFSG.Certificates.Kernel.U4FFLocCheckSound
import Certificates.Kernel.U4FFLoc.W000
import Certificates.Kernel.U4FFLoc.W100
import Certificates.Kernel.U4FFLoc.W010
import Certificates.Kernel.U4FFLoc.W001
import Certificates.Kernel.U4FFLoc.W110
import Certificates.Kernel.U4FFLoc.W101
import Certificates.Kernel.U4FFLoc.W011
import Certificates.Kernel.U4FFLoc.W111

public section

namespace Certificates

open CFSG.KC.U4FFLoc Kernel.U4FFLoc

theorem certificate27980 : ∀ a b c : Bool, CFSG.HardMathSupport.U4FF.LocValid a b c := by
  intro a b c
  rw [locValid_iff]
  cases a <;> cases b <;> cases c <;>
    simp only [LocValidK, loc1_000, loc2_000, loc3_000, loc1_100, loc2_100, loc3_100, loc1_010,
      loc2_010, loc3_010, loc1_001, loc2_001, loc3_001, loc1_110, loc2_110, loc3_110, loc1_101,
      loc2_101, loc3_101, loc1_011, loc2_011, loc3_011, loc1_111, loc2_111, loc3_111,
      Bool.and_self]

end Certificates
