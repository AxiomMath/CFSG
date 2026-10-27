module

public import Certificates.Data.Kernel.ActLB
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointInputs
public import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Benes
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each

public section

#kc_repo #kc_nat_items_gz CFSG.KD.L1649001 "Certificates/Kernel/CosPres/data/L1649001.items.gz" 1161288 3147297085542868047
  F[36]

namespace CFSG.KD.L1649001

open CFSG.KC CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.ActLB CFSG.StandardType.QTwo.SixPoint

#kc_select CFSG.KD.L1649001 Fs F 36
#kc_benes CFSG.KD.L1649001 N 0 36 13 fun _ c => colPlanes (Fs c) 32 8064 13 0
#kc_select CFSG.KD.L1649001 Nf N 36

@[expose] noncomputable def ch1649001net (c : Nat) : Bool := netOK 13 (Nf c)

@[expose] noncomputable def ch1649001fix (i : Nat) : Bool :=
  fixK 13 (Nf (Nat.mul 2 (chart5.getD i 0))) 0

#kc_each ch1649001net 0 36
#kc_each ch1649001fix 0 14

set_option maxRecDepth 100000 in
theorem ch1649001rels : relsOK 13 36 Nf (codesOf relsP) = true := by
  quickRfl

set_option maxRecDepth 100000 in
theorem ch1649001inv : relsOK 13 36 Nf (invPairs 18) = true := by
  quickRfl

set_option maxRecDepth 100000 in
theorem ch1649001orb : orbitOK 13 (nets 36 Nf) 0 7 (ones 8064) = true := by
  quickRfl

end CFSG.KD.L1649001

end
