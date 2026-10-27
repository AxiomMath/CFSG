module

public import CFSG.Monster.B.TwoA.Fischer.AmbientRootOrbit

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent AddSubgroupClass.instZModModule

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Fischer
  CFSG.Monster.B.Fischer CFSG.Monster.B.Classical.Mog22 CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Fischer
  CFSG.Monster.B.Fischer CFSG.Monster.B.Classical.Mog22 CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

namespace CertificateChecks.Batch16003

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Fischer
  CFSG.Monster.B.Fischer CFSG.Monster.B.Classical.Mog22 CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

private theorem seedLabels_nodup_0 : Cert.seedLabels.Nodup := by
  decide +kernel

private theorem seedLabels_lt_1 : ∀ n ∈ Cert.seedLabels, n < 3510 := by
  decide +kernel

end CertificateChecks.Batch16003

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Fischer
  CFSG.Monster.B.Fischer CFSG.Monster.B.Classical.Mog22 CFSG.Sporadic.SmallF2 in
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension in
open scoped Matrix IsMulCommutative in
theorem certificate16003 : (
    Cert.seedLabels.Nodup
  ) ∧ (
    ∀ n ∈ Cert.seedLabels, n < 3510
  ) := by
  exact ⟨CertificateChecks.Batch16003.seedLabels_nodup_0, CertificateChecks.Batch16003.seedLabels_lt_1⟩

end Certificates
