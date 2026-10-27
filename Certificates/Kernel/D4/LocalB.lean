module

public import Certificates.Kernel.D4.EnumB
public import Certificates.Kernel.D4.Tabs
public import Certificates.Kernel.D4.Wit
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.D4LocalK
public meta import Certificates.Data.Item434D42
public meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Check
public meta import Certificates.Kernel.LocalComp.BfsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KC.B3S3K CFSG.KC.D4Local

meta def locB : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 2457 12 d4CBGens).1
  let uf := pts.map (uFlag 2457 d4Lines[1]!)
  let yf := Array.ofFn (n := pts.size) fun i => yFlag 2457 2457 pts[i.val]! d4SelfPtB[i.val]!
  let idx := fun (fl : Array Bool) => (List.range fl.size).filter fun i => fl[i]!
  let rk := fun (fl : Array Bool) => (flagRanks fl).toList ++ [flagCount fl]
  idx uf ++ idx yf ++ rk uf ++ rk yf

end CertificateChecks.KernelD4

end

#kss_natlist CertificateChecks.KernelD4.LB CertificateChecks.KernelD4.locB

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KC.B3S3K CFSG.KC.D4Local

@[expose] noncomputable def UIB (a : Nat) : Nat := LB a

@[expose] noncomputable def YIB (b : Nat) : Nat := LB (Nat.add 168 b)

@[expose] noncomputable def RUB (i : Nat) : Nat := LB (Nat.add 231 i)

@[expose] noncomputable def RYB (i : Nat) : Nat := LB (Nat.add 880 i)

@[expose] noncomputable def SPB (i : Nat) : Nat := wget 16 WX.F (Nat.add 1512 i)

@[expose] noncomputable def PWB (j : Nat) : Nat := wget 16 WX.F (Nat.add 49032 j)

@[expose] noncomputable def rkUB (s : Nat) : Bool :=
  allBlk (Nat.mul 54 s) (rankAt (fun i => uFlagK 2457 12 (LX 1) (pw 2457 12 (LX 1) 2) (EB.T i))
    UIB RUB) 54

@[expose] noncomputable def rkYB (s : Nat) : Bool :=
  allBlk (Nat.mul 54 s) (rankAt (fun i => yFlagK 2457 12 2457 (EB.T i) (SPB i)) YIB RYB) 54

@[expose] noncomputable def prB (s : Nat) : Bool :=
  allBlk (Nat.mul 8 s) (pairsK 2457 12 2457 EB.T UIB YIB PWB 63) 8

theorem endsB : rankEnds 648 RUB 168 = true ∧ rankEnds 648 RYB 63 = true :=
  ⟨by quickRfl, by quickRfl⟩

end CertificateChecks.KernelD4

end

#kss_each CertificateChecks.KernelD4.RKUB CertificateChecks.KernelD4.rkUB 12
#kss_each CertificateChecks.KernelD4.RKYB CertificateChecks.KernelD4.rkYB 12
#kss_each CertificateChecks.KernelD4.PRB CertificateChecks.KernelD4.prB 21
