module

public import Certificates.Kernel.C21205.CritData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachStep
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CFSG.KD.C21205C

open CFSG.KC.C21205 CFSG.LargeExtraspecial.AS35QCo.Native

theorem ch21205k1_crit : critK (repc 1) nA1 A1 B1 O1 F1 W1 D1 4608 = true := by quickRfl

theorem ch21205k1_len : Nat.beq (List.length D1) 9 = true := by quickRfl

@[expose] noncomputable def ch21205k1 (i : Nat) : Bool :=
  chunkK (repc 1) nA1 A1 B1 F1 W1 S1 (chunkAt D1 i)

@[expose] noncomputable def ch21205s1 (i : Nat) : Bool := scanK (repc 1) S1 (chunkAt D1 i)

#kc_each_step ch21205k1 0 9 1 as ch21205k1_
#kc_forall_chunks ch21205k1_all (fun i => ch21205k1 i = true) 9 ch21205k1_ 1
#kc_each_step ch21205s1 0 9 1 as ch21205s1_
#kc_forall_chunks ch21205s1_all (fun i => ch21205s1 i = true) 9 ch21205s1_ 1

end CFSG.KD.C21205C

end
