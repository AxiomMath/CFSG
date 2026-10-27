module

public import CFSG.Certificates.Kernel.N7A7PackSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.CGT.T75JM.N6Branch
public import Mathlib

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CFSG.KernelN7

open CFSG.CGT.T75M23

theorem packP_a7x : packP a7x = 1726081 := by decide +kernel

theorem packP_a7y : packP a7y = 1221360 := by decide +kernel

theorem a7_noDup : noDupB (a7Words.map (wordP 1726081 1221360)) 0 = true := by quickRfl

theorem a7Nodup_ok : A7Nodup := a7Nodup_of_noDupB packP_a7x packP_a7y a7_noDup

end CFSG.KernelN7
