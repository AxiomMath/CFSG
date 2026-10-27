module

public import CFSG.Monster.B.E6.StdF4HeckePanel
public import CFSG.Monster.B.E6.StdF4Points

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical

namespace CertificateChecks.Batch16029

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical

private theorem plen_eq_zero_iff_0 : ∀ β < 24, plen β = 0 → β = 23 := by
  decide +kernel

end CertificateChecks.Batch16029

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical in
theorem certificate16029 : ∀ β < 24, plen β = 0 → β = 23 := by
  exact CertificateChecks.Batch16029.plen_eq_zero_iff_0

end Certificates
