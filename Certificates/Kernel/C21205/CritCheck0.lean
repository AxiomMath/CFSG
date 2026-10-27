module

public import Certificates.Kernel.C21205.CritData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachStep
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CFSG.KD.C21205C

open CFSG.KC.C21205 CFSG.LargeExtraspecial.AS35QCo.Native

theorem ch21205k0_crit : critK (repc 0) nA0 A0 B0 O0 F0 W0 D0 23040 = true := by quickRfl

theorem ch21205k0_len : Nat.beq (List.length D0) 45 = true := by quickRfl

theorem ch21205k0_s : Nat.beq (List.length S0) 0 = true := by quickRfl

@[expose] noncomputable def ch21205k0 (i : Nat) : Bool :=
  chunkK (repc 0) nA0 A0 B0 F0 W0 S0 (chunkAt D0 i)

#kc_each_step ch21205k0 0 45 1 as ch21205k0_
#kc_forall_chunks ch21205k0_all (fun i => ch21205k0 i = true) 45 ch21205k0_ 1

end CFSG.KD.C21205C

end
