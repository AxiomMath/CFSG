module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
import CFSG.RankThree.PartTwo.Sec11.Item1119ProofBasic

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Inverter1118Proof

section Group

variable {G : Type*} [Group G]

theorem conj_zpow_eq_inv {j y : G} (hj : j * y * j⁻¹ = y⁻¹) (n : ℤ) :
    j * y ^ n * j⁻¹ = (y ^ n)⁻¹ := by
  rw [← conj_zpow, hj, inv_zpow]

theorem inverts_of_mem_zpowers {j y z : G} (hj : j * y * j⁻¹ = y⁻¹)
    (hz : z ∈ Subgroup.zpowers y) : j * z * j⁻¹ = z⁻¹ := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact conj_zpow_eq_inv hj m

end Group

end Inverter1118Proof

end CFSG.RankThree.PartTwo.Sec11
