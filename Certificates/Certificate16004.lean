module

public import CFSG.YGroups.Y443.Native.AlignAlg
public import CFSG.YGroups.Y443.Tri.Parabolic2

public section

open CFSG CFSG.YGroups CFSG.YGroups.Y443 CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.Monster.Generated CFSG.Open

namespace CertificateChecks.Batch16004

open CFSG CFSG.YGroups CFSG.YGroups.Y443 CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.Monster.Generated CFSG.Open

private theorem slet_map_ρL_0 : slet.map ρL =
    (List.replicate 9 [0, 5, 6, 7, 1, 2, 9]).flatten ++
      (List.replicate 9 [0, 9, 10, 11, 5, 6, 1]).flatten := by
  decide +kernel

private theorem slet_map_ρL_le_1 : ∀ c ∈ slet.map ρL, c ≤ 11 := by
  decide +kernel

end CertificateChecks.Batch16004

namespace Certificates

open CertificateChecks

open CFSG CFSG.YGroups CFSG.YGroups.Y443 CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.Monster.Generated CFSG.Open in
theorem certificate16004 : (
    slet.map ρL =
      (List.replicate 9 [0, 5, 6, 7, 1, 2, 9]).flatten ++
        (List.replicate 9 [0, 9, 10, 11, 5, 6, 1]).flatten
  ) ∧ (
    ∀ c ∈ slet.map ρL, c ≤ 11
  ) := by
  exact ⟨CertificateChecks.Batch16004.slet_map_ρL_0, CertificateChecks.Batch16004.slet_map_ρL_le_1⟩

end Certificates
