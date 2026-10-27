module

public import Certificates.Kernel.MonsterB.Short3014Orbit
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.B.Short.AxisAction
public import CFSG.Monster.B.Short.OrbitCertBase
public import CFSG.Monster.B.Short.OrbitSpec

public section

namespace CertificateChecks.KernelAP.Baby

open CFSG.KLie.CT CFSG.KC.SortTree

@[expose] noncomputable def PT : Nat :=
  47758914269546354982683078068829456704164423862093743397580034411621752859030

@[expose] noncomputable def condD (u : Nat) : Bool :=
  andB (notB (Nat.beq u 12288))
    (andB (Nat.beq (Nat.land (Nat.shiftRight PT (Nat.land u 191)) 1) 0)
      (notB (CertificateChecks.Short3014.memS (Nat.xor u 12288))))

@[expose] noncomputable def indD (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 1 (condD (valF 24 (CertificateChecks.Short3014.recS i)))

@[expose] noncomputable def cntC (c : Nat) : Nat :=
  sumN 1890 fun j => indD (Nat.add (Nat.mul c 1890) j)

@[expose] noncomputable def PC : Nat :=
  15011753192896695695376762913449032492051596298970326524705915048845911427727822341526170626635387964337180852351095930060250891562525171487374389533474636463607980969519644919967239447345

@[expose] noncomputable def chunkD (c : Nat) : Bool := Nat.beq (cntC c) (fget PC c 12)

@[expose] noncomputable def sliceD (o m : Nat) : Bool := allN m fun j => chunkD (Nat.add o j)

set_option maxRecDepth 100000

theorem d0 : sliceD 0 4 = true := by quickRfl
theorem d1 : sliceD 4 4 = true := by quickRfl
theorem d2 : sliceD 8 4 = true := by quickRfl
theorem d3 : sliceD 12 4 = true := by quickRfl
theorem d4 : sliceD 16 4 = true := by quickRfl
theorem d5 : sliceD 20 4 = true := by quickRfl
theorem d6 : sliceD 24 4 = true := by quickRfl
theorem d7 : sliceD 28 4 = true := by quickRfl
theorem d8 : sliceD 32 4 = true := by quickRfl
theorem d9 : sliceD 36 4 = true := by quickRfl
theorem d10 : sliceD 40 4 = true := by quickRfl
theorem d11 : sliceD 44 4 = true := by quickRfl
theorem d12 : sliceD 48 4 = true := by quickRfl

theorem total : Nat.beq (sumN 52 fun c => fget PC c 12) 46575 = true := by quickRfl

end CertificateChecks.KernelAP.Baby

end
