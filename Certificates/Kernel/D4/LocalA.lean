module

public import Certificates.Kernel.D4.EnumA
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

meta def locA : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 2457 12 d4CAGens).1
  let uf := pts.map (uFlag 2457 d4Lines[0]!)
  let yf := Array.ofFn (n := pts.size) fun i => yFlag 2457 2457 pts[i.val]! d4SelfPtA[i.val]!
  let idx := fun (fl : Array Bool) => (List.range fl.size).filter fun i => fl[i]!
  let rk := fun (fl : Array Bool) => (flagRanks fl).toList ++ [flagCount fl]
  idx uf ++ idx yf ++ rk uf ++ rk yf

end CertificateChecks.KernelD4

end

#kss_natlist CertificateChecks.KernelD4.LA CertificateChecks.KernelD4.locA

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KC.B3S3K CFSG.KC.D4Local

@[expose] noncomputable def UIA (a : Nat) : Nat := LA a

@[expose] noncomputable def YIA (b : Nat) : Nat := LA (Nat.add 168 b)

@[expose] noncomputable def RUA (i : Nat) : Nat := LA (Nat.add 447 i)

@[expose] noncomputable def RYA (i : Nat) : Nat := LA (Nat.add 1960 i)

@[expose] noncomputable def SPA (i : Nat) : Nat := wget 16 WX.F i

@[expose] noncomputable def PWA (j : Nat) : Nat := wget 16 WX.F (Nat.add 2160 j)

@[expose] noncomputable def rkUA (s : Nat) : Bool :=
  allBlk (Nat.mul 56 s) (rankAt (fun i => uFlagK 2457 12 (LX 0) (pw 2457 12 (LX 0) 2) (EA.T i))
    UIA RUA) 56

@[expose] noncomputable def rkYA (s : Nat) : Bool :=
  allBlk (Nat.mul 56 s) (rankAt (fun i => yFlagK 2457 12 2457 (EA.T i) (SPA i)) YIA RYA) 56

@[expose] noncomputable def prA (s : Nat) : Bool :=
  allBlk (Nat.mul 8 s) (pairsK 2457 12 2457 EA.T UIA YIA PWA 279) 8

theorem endsA : rankEnds 1512 RUA 168 = true ∧ rankEnds 1512 RYA 279 = true :=
  ⟨by quickRfl, by quickRfl⟩

end CertificateChecks.KernelD4

end

#kss_each CertificateChecks.KernelD4.RKUA CertificateChecks.KernelD4.rkUA 27
#kss_each CertificateChecks.KernelD4.RKYA CertificateChecks.KernelD4.rkYA 27
#kss_each CertificateChecks.KernelD4.PRA CertificateChecks.KernelD4.prA 21
