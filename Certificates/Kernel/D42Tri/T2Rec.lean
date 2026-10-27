module

public import Certificates.Kernel.D42Tri.T2Data
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulH
public import Certificates.Data.Kernel.D42T2
public import Certificates.Kernel.OmegaEight.Arr3009K
meta import Certificates.Kernel.D42Tri.T2Data
meta import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Data.D42Triality
meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD42Tri.T2M

meta def wM (w : List Nat) : Array Nat :=
  w.foldl (fun a l => CFSG.KS.RawGen.comp 360 a CFSG.EvenSmallLie.OmegaEight.genArrs[l]!)
    (Array.range 360)

meta def gM : Array (Array Nat) :=
  #[wM CertificateChecks.KernelD42Tri.TD.w5, wM CertificateChecks.KernelD42Tri.TD.w6]

meta def giM : Array (Array Nat) := gM.map (CFSG.KS.RawGen.inv 360)

meta def tM : Array Nat :=
  CFSG.Sporadic.SmallOddCore.Native.natArr
    (CFSG.Sporadic.SmallOddCore.Native.hexT 3 360 0
      CFSG.HardMathSupport.Dickson.Bal207.D42TriData.repHex)

end CertificateChecks.KernelD42Tri.T2M

#kmulh CertificateChecks.KernelD42Tri.TC 360 9 CertificateChecks.KernelD42Tri.T2M.gM
  CertificateChecks.KernelD42Tri.T2M.giM CertificateChecks.KernelD42Tri.T2M.tM 72

namespace CertificateChecks.KernelD42Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.CommBase
  CFSG.KC.D42T2 CertificateChecks.KernelO8

theorem t2Pt : bAnd(pm (T2H.F 0), bAnd(Nat.beq (pg 9 (mask 9) (T2H.F 0) 1) 178,
    Nat.beq (pg 9 (mask 9) (T2H.F 0) 178) 242)) = true := by
  quickRfl

theorem t2Words : bAnd(allL (lettersOK 8) [TD.w1, TD.w2, TD.w3, TD.w4, TD.w5, TD.w6],
    bAnd(allL (fun W => Nat.beq (wapp 9 (mask 9) AP.S W 1) 1)
      [TD.w1, TD.w2, TD.w3, TD.w4, TD.w5, TD.w6],
    bAnd(allL (fun W => Nat.beq (wapp 9 (mask 9) AP.S W 178) 178) [TD.w3, TD.w4, TD.w5, TD.w6],
      allL (fun W => Nat.beq (wapp 9 (mask 9) AP.S W 242) 242) [TD.w5, TD.w6]))) = true := by
  quickRfl

theorem t2Orb0 : bAnd(orbOK 360 (fun l q => pg 9 (mask 9) (AP.S l) q) 8 1 TD.o0p TD.o0q TD.o0l,
    Nat.beq TD.o0p.length 120) = true := by
  quickRfl

theorem t2Orb1 : bAnd(orbOK 360 (fun l q => wapp 9 (mask 9) AP.S ([TD.w1, TD.w2].getD l []) q)
    2 178 TD.o1p TD.o1q TD.o1l, Nat.beq TD.o1p.length 120) = true := by
  quickRfl

theorem t2Orb2 : bAnd(orbOK 360 (fun l q => wapp 9 (mask 9) AP.S ([TD.w3, TD.w4].getD l []) q)
    2 242 TD.o2p TD.o2q TD.o2l, Nat.beq TD.o2p.length 56) = true := by
  quickRfl

theorem tcBind : bAnd(allN 2 (fun j => bAnd(allN 360 (fun q => Nat.beq (pg 9 (mask 9) (TC.G j) q)
      (wapp 9 (mask 9) AP.S ([TD.w5, TD.w6].getD j []) q)),
      permOK 360 9 (mask 9) (360 * 9) (TC.G j) (TC.GI j))),
    Nat.beq TC.R (T2H.F 0)) = true := by
  quickRfl

theorem tcCanon : bAnd(allN 2 (fun j => bAnd(canonK 360 9 (mask 9) (360 * 9) (TC.G j),
      canonK 360 9 (mask 9) (360 * 9) (TC.GI j))),
    bAnd(canonK 360 9 (mask 9) (360 * 9) TC.R, szOK 360 9)) = true := by
  quickRfl

theorem tcCnt : Nat.beq TC.cnt 72 = true := by quickRfl

theorem tcHd : penumHdK TC.R TC.cnt 72 TC.T TC.PL = true := by quickRfl

theorem tcPen : penumSlK 360 9 (mask 9) (360 * 9) true TC.G TC.GI 2 TC.cnt TC.T TC.PL TC.POS
    TC.SRT TC.SRI 0 72 = true := by
  quickRfl

theorem tcHs : slK TC.cnt (hsortPtK 360 9 (mask 9) TC.cnt TC.T TC.HS TC.HSI) 0 72 = true := by
  quickRfl

end CertificateChecks.KernelD42Tri

end
