module

public import Certificates.Kernel.VecCert.Co1.A
public import CFSG.Certificates.Kernel.Co1M.OrbitMem
public import CFSG.Certificates.Kernel.VecKSound
public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import Certificates.Kernel.VecCert.Gen
import CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command CFSG.KC.VecGen in
elab "#co1m_orbHyps" : command => liftCoreM <| withOptions (Elab.async.set · false) do
  let P := `CertificateChecks.KernelVec.Co1
  let DE := mkApp (mkConst ``CFSG.Sporadic.Co1.Native.co1Data) (mkConst ``Unit.unit)
  let pj := fun (f : Name) => mkApp (mkConst (``CFSG.Sporadic.SmallF2.Native.VecData ++ f)) DE
  let c := fun (nm : Name) => mkConst (P ++ nm)
  let nE := pj `n
  let K := `CFSG.KC.VecK
  let fs : List (Name × String × Expr) := [
    (`cmHorb, "orb", mkAppN (mkConst (K ++ `orbAt)) #[pj `d, nE, c `NA, c `NB, c `Pt, c `AT, c `BT]),
    (`cmHbfs, "bfs", mkAppN (mkConst (K ++ `bfsAt)) #[nE, c `AT, c `BT, c `FO]),
    (`cmHsort, "sort", mkAppN (mkConst (K ++ `sortAt)) #[nE, c `Pt, c `S, c `IP, c `SP])]
  for (nm, tag, f) in fs do
    let pf ← coverOf P (fun _ => false) tag f nE 98280 256
    let ty ← Meta.MetaM.run' (Meta.inferType pf)
    addThm (`CertificateChecks.KernelCo1M ++ nm) ty pf

public section

set_option maxRecDepth 200000

#co1m_orbHyps

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KC.VecK CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelVec.Co1

theorem cm_seed : seedK csA csB (CFSG.Sporadic.Co1.Native.co1Data ()).d MA MB NA NB
    (CFSG.Sporadic.Co1.Native.co1Data ()).expA (CFSG.Sporadic.Co1.Native.co1Data ()).expB = true := by
  quickRfl

theorem cm_orb_twin :
    ((CFSG.Sporadic.Co1.Native.co1Data ()).orbit ()).pts.size = 98280 ∧
      (∀ i < 98280, ((CFSG.Sporadic.Co1.Native.co1Data ()).orbit ()).pts[i]! = lk Pt 32 i) ∧
      ∀ w, CFSG.Sporadic.Co1.OddNative.inPts ((CFSG.Sporadic.Co1.Native.co1Data ()).orbit ()).pts
        (posTable 24 ((CFSG.Sporadic.Co1.Native.co1Data ()).orbit ()).pts) 98280 w =
        orbMemK 98280 (lk S 32) 17 w :=
  orbit_twin (CFSG.Sporadic.Co1.Native.co1Data ()) 17 hA hB cm_seed (by quickRfl) (by quickRfl)
    cmHorb cmHbfs cmHsort (by quickRfl)

theorem cm_orb_inPts (w : Nat) :
    CFSG.Sporadic.Co1.OddNative.inPts ((CFSG.Sporadic.Co1.Native.co1Data ()).orbit ()).pts
      (posTable 24 ((CFSG.Sporadic.Co1.Native.co1Data ()).orbit ()).pts) 98280 w =
      orbMemK 98280 (lk S 32) 17 w :=
  cm_orb_twin.2.2 w

end CertificateChecks.KernelCo1M

end
