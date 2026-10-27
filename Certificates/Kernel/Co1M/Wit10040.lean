module

public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1M.Data10037
public import Certificates.Kernel.Co1M.Data10041
public import Certificates.Data.Kernel.GmsWitK
public import CFSG.Monster.GMS.S365CentWitSpecInputs
public meta import Certificates.Kernel.VecCert.Gen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.GMS.S365CentDefs
public import CFSG.Monster.GMS.S365CentPathSpec
public import CFSG.Monster.GMS.S365CentRootSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

@[expose] noncomputable def wit40 (j : Nat) : Bool :=
  CFSG.KC.GmsPath.witAt CFSG.KD.Co1M.QP CFSG.KD.Co1M.MX CFSG.KD.Co1M.MY
    [CFSG.KD.Co1M.CT0, CFSG.KD.Co1M.CT1, CFSG.KD.Co1M.CT2] CFSG.Monster.GMS.S365.wordA
    CFSG.Monster.GMS.S365.wordB (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 98280 17 j

end CertificateChecks.KernelCo1M

open Lean Elab Command CFSG.KC.VecGen in
elab "#c10040_wit" : command => liftCoreM <| withOptions (Elab.async.set · false) do
  let P := `CertificateChecks.KernelCo1M
  let f := mkConst ``CertificateChecks.KernelCo1M.wit40
  let pf ← coverOf (P ++ `W40) (fun _ => true) "wit" f (mkRawNatLit 98280) 98280 256
  let ty ← Meta.MetaM.run' (Meta.inferType pf)
  addThm (P ++ `wit40All) ty pf

#c10040_wit

end
