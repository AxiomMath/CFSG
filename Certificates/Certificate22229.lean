module

public import Certificates.Data.GrSLitL34FactsCF23U52Data
import Certificates.Kernel.SchreierFam.U52Chain
import CFSG.Certificates.Kernel.Misc.ArrBind
import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue

namespace CertificateChecks.Batch22229

open CFSG.ComponentClassification.GSThmB.U52 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
  CFSG.KC.Misc.ArrEnum CertificateChecks.KernelSchreierFam CFSG.Certificates.Native

theorem binds22229 : Binds 341 9 U52.S 9 5 U52.BP chainS baseArr :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel,
    fun j hj => arrBind_sound (U52.bS j hj), by decide +kernel, U52.bget⟩

theorem words22229 : chainW = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 9 dU52 :=
  wordsArr_eq (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem chain22229 : rawChainOK 341 (chainS.extract 0 2) chainS baseArr chainW 4 = true := by
  rw [words22229]
  exact rawChainK_sound binds22229 U52.head U52.hl U52.hNS U52.hs

theorem orbits22229 : (rawOrbitSizes 341 chainS baseArr).prod = 13685760 := by
  rw [rawOrbitSizesK_sound binds22229 U52.perm U52.hl]
  exact U52.orbProd

end CertificateChecks.Batch22229

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GSThmB.U52 CFSG.Certificates.Native in
theorem certificate22229 : rawChainOK 341 (chainS.extract 0 2) chainS baseArr chainW 4 = true ∧
    (rawOrbitSizes 341 chainS baseArr).prod = 13685760 :=
  ⟨CertificateChecks.Batch22229.chain22229, CertificateChecks.Batch22229.orbits22229⟩

end Certificates
