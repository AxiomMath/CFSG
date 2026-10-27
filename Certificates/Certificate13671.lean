
module

public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Open.GLADefs
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Kernel.Co1FiveL.GlueT
import CFSG.Sporadic.Co1Block.PermCheckInputs
meta import CFSG.Sporadic.Co1Block.PermData
meta import CFSG.Sporadic.Schreier.Co1StabFix
meta import CFSG.Sporadic.Schreier.Co1StabCheck
meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
meta import Certificates.Data.CFSGNative.Co1Schreier.Base
meta import Certificates.Data.CFSGNative.Co1.Data
meta import Certificates.Data.CFSGNative.HS.SmallF2
meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
import CFSG.Sporadic.Schreier.Co1OrbEnum
import CFSG.Sporadic.Schreier.Co1XSet
import CFSG.Sporadic.Schreier.Co1StabCheckInputs
meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
meta import CFSG.Sporadic.Schreier.Co1StabData
meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
meta import Certificates.Data.CFSGNative.Th.Tables
meta import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace Certificates

open CFSG.Sporadic.Co1Schreier Timmesfeld.Co1Five in
theorem certificate13671 : ∀ τ < 3, ∀ x y : ↥CFSG.Sporadic.Co1Schreier.GA,
    MRep (a0Row (Timmesfeld.Co1Five.gDag CFSG.Sporadic.Co1.Native.co1Data.rowsA
      CFSG.Sporadic.Co1.Native.co1Data.rowsB).1 (repA.getD τ 0)) (x : GL24) →
    MRep (a0Row (Timmesfeld.Co1Five.gDag CFSG.Sporadic.Co1.Native.co1Data.rowsA
      CFSG.Sporadic.Co1.Native.co1Data.rowsB).1 (repB.getD τ 0)) (y : GL24) →
    Nat.card (Subgroup.centralizer ({x, y} : Set ↥CFSG.Sporadic.Co1Schreier.GA)) = 125 * leafR.getD τ 0 ∧
      CFSG.Open.GLAPPrimeCoreOf 5 (Subgroup.centralizer ({x, y} : Set ↥CFSG.Sporadic.Co1Schreier.GA)) = ⊥ :=
  fun _ hτ _ _ hx hy => CertificateChecks.KernelCo1FiveL.planes hτ hx hy

end Certificates
