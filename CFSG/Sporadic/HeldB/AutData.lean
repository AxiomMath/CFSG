module

public import CFSG.Sporadic.HeldB.CertPChain

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def heAutRHex : String := include_str "Data"/"AutR.txt"

@[expose] def heAutRArr : Array ℕ := hexTable 4 8330 0 heAutRHex

@[expose] def heAutR : Equiv.Perm (Fin 8330) := permOfArr 8330 heAutRArr

@[expose] def heAutU : Equiv.Perm (Fin 8330) := heAutR ^ 5

@[expose] def heAutGroup : Subgroup (Equiv.Perm (Fin 8330)) := heP ⊔ Subgroup.zpowers heAutU

end CFSG.Sporadic.HeldB
