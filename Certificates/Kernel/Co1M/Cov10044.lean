module

public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Sporadic.Co1.Module.InvAssemble
public import CFSG.Monster.GMS.Facts.Co1OddPairs
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Monster.GMS.S365RootInputs
public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1M.Data10044
public meta import Certificates.Kernel.VecCert.Gen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10073Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.VecK CFSG.KD.Co1M CFSG.Sporadic.Co1.Module.Pairs

@[expose] noncomputable def covF44 (p : Nat) : Bool :=
  !orthAll rootGs (lk CertificateChecks.KernelVec.Co1.Pt 32 p) ||
    TL.contains (lk CertificateChecks.KernelVec.Co1.Pt 32 p)

end CertificateChecks.KernelCo1M

open Lean Elab Command CFSG.KC.VecGen in
elab "#c10044_cover" : command => liftCoreM <| withOptions (Elab.async.set · false) do
  let P := `CertificateChecks.KernelCo1M
  let f := mkConst ``CertificateChecks.KernelCo1M.covF44
  let pf ← coverOf (P ++ `C44) (fun _ => true) "cov" f (mkRawNatLit 98280) 98280 256
  let ty ← Meta.MetaM.run' (Meta.inferType pf)
  addThm (P ++ `cov44All) ty pf

#c10044_cover

end
