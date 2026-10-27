module

public import Certificates.Data.Odd87F3McL
public meta import Certificates.Data.Odd87F3McL
import CFSG.Certificates.Kernel.Odd87CCKSound
import Certificates.Kernel.Odd87CC.McLC1
import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.HeModelKSound
import CFSG.Certificates.Kernel.HexaKSound
import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Odd87CCK CertificateChecks.KernelLC.McLC

theorem certificate5160 : Certificates.Odd87F3.McL.mclCCOK = true := by
  have hT : ∀ k < 22, CFSG.Sporadic.SmallOddCore.mclCentTbl k = CFSG.KC.Child3.tabP 275 9 (MC.F k) :=
    fun k hk => table_eq_tabP (natArr_cent k hk)
  have e : [CFSG.Sporadic.SmallOddCore.mclCentTbl 18, CFSG.Sporadic.SmallOddCore.mclCentTbl 19,
      CFSG.Sporadic.SmallOddCore.mclCentTbl 20, CFSG.Sporadic.SmallOddCore.mclCentTbl 21] =
      KernelOdd87CC.McLC1.gens.map (CFSG.KC.Child3.tabP 275 9) := by
    simp only [KernelOdd87CC.McLC1.gens, List.map_cons, List.map_nil, hT 18 (by norm_num),
      hT 19 (by norm_num), hT 20 (by norm_num), hT 21 (by norm_num)]
  unfold Certificates.Odd87F3.McL.mclCCOK
  rw [e]
  exact ccOK_of_ccK (by rfl) KernelOdd87CC.McLC1.chk

end Certificates
