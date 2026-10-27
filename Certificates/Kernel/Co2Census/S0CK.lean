module

public import Certificates.Kernel.Co2Census.S0Defs
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

@[expose] noncomputable def centMisc (Pt G GR : Nat → Nat) (ng nr : Nat) : Bool :=
  Nat.beq (Pt 0) IDP && (List.range ng).all fun l => Nat.beq (GR l) (SK (G l)) &&
    Nat.beq (mulV (GR l) (SK nr)) (mulV (SK nr) (GR l))

theorem C2331_tree : ∀ i < 4608, treeK (rmStep C2331GRt) 2 4608 C2331Pt C2331Xt i = true := by
  kc_cover 512

theorem C2331_clos : ∀ i < 4608, closK (rmStep C2331GRt) 2 4608 C2331Pt C2331Xt i = true := by
  kc_cover 512

theorem C2331_root : ∀ i < 4608, Nat.beq (rtOf C2331Xt i) 0 = true := by
  kc_cover 1024

theorem C2331_misc : centMisc C2331Pt C2331Gt C2331GRt 2 2331 = true := by
  decide +kernel

theorem C144_tree : ∀ i < 384, treeK (rmStep C144GRt) 3 384 C144Pt C144Xt i = true := by
  kc_cover 128

theorem C144_clos : ∀ i < 384, closK (rmStep C144GRt) 3 384 C144Pt C144Xt i = true := by
  kc_cover 128

theorem C144_root : ∀ i < 384, Nat.beq (rtOf C144Xt i) 0 = true := by
  kc_cover 384

theorem C144_misc : centMisc C144Pt C144Gt C144GRt 3 144 = true := by
  decide +kernel

theorem C1082_tree : ∀ i < 1536, treeK (rmStep C1082GRt) 3 1536 C1082Pt C1082Xt i = true := by
  kc_cover 512

theorem C1082_clos : ∀ i < 1536, closK (rmStep C1082GRt) 3 1536 C1082Pt C1082Xt i = true := by
  kc_cover 512

theorem C1082_root : ∀ i < 1536, Nat.beq (rtOf C1082Xt i) 0 = true := by
  kc_cover 1024

theorem C1082_misc : centMisc C1082Pt C1082Gt C1082GRt 3 1082 = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
