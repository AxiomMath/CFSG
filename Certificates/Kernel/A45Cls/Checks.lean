module

public import Certificates.Kernel.A45Cls.Cls
public import Certificates.Kernel.A45Cls.Grp
public import Certificates.Data.Kernel.A45Cls.Defs
public import Certificates.Data.Kernel.PermCent.CV

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.Certificates.Kernel.PkCV
  CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] noncomputable def memCls (v : Nat) : Bool :=
  memK 45 6 ps KA.N KA.T KA.S v || memK 45 6 ps KB.N KB.T KB.S v ||
    memK 45 6 ps K36.N K36.T K36.S v || memK 45 6 ps K540.N K540.T K540.S v

@[expose] noncomputable def coverK (N : Nat) (T : Nat → Nat) : Bool :=
  allN N fun i => strictB (T i) fun v => !isInvK 45 6 v || memCls v

theorem binds :
    (cOf x45).1 = KA.G 0 ∧ (cOf y45).1 = KA.G 1 ∧ (cOf f45).1 = KA.G 2 ∧
    KB.G 0 = KA.G 0 ∧ KB.G 1 = KA.G 1 ∧ KB.G 2 = KA.G 2 ∧
    K36.G 0 = KA.G 0 ∧ K36.G 1 = KA.G 1 ∧ K36.G 2 = KA.G 2 ∧
    K540.G 0 = KA.G 0 ∧ K540.G 1 = KA.G 1 ∧ K540.G 2 = KA.G 2 ∧
    (cOf (Certificates.P43Twin.tA ())).1 = KA.T KA.r0 ∧
    (cOf (Certificates.P43Twin.tB ())).1 = KB.T KB.r0 ∧
    (cOf (Certificates.P43Twin.t36 ())).1 = K36.T K36.r0 ∧
    (cOf (Certificates.P43Twin.t540 ())).1 = K540.T K540.r0 := by
  decide +kernel

theorem words : bindWs 45 6 3 KA.G SY.G sW 0 = true ∧ bindWs 45 6 3 KA.G CA.G cW 0 = true := by
  decide +kernel

theorem orders : KA.N = 45 ∧ KB.N = 270 ∧ K36.N = 36 ∧ K540.N = 540 ∧ KA.ng = 3 ∧
    KB.ng = 3 ∧ K36.ng = 3 ∧ K540.ng = 3 ∧ SY.N = 128 ∧ SY.ng = 4 ∧ CA.N = 1152 ∧ CA.ng = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ids : SY.T 0 = pidn 45 6 ∧ CA.T 0 = pidn 45 6 := by decide +kernel

theorem fixes : fixK 45 6 (KA.T KA.r0) = 13 ∧ fixK 45 6 (KB.T KB.r0) = 5 ∧
    fixK 45 6 (K36.T K36.r0) = 15 ∧ fixK 45 6 (K540.T K540.r0) = 7 := by
  decide +kernel

theorem cover : coverK SY.N SY.T = true := by decide +kernel

theorem cent : allN 3 (fun k => eq22 45 6 (mask 6) (CA.G k) (KA.T KA.r0) (KA.T KA.r0) (CA.G k)) =
    true := by
  decide +kernel

end CertificateChecks.KernelA45

end
