module

public import CFSG.Sporadic.HNSchreier.Sylow3
public import CFSG.Assembly.Defs
public import Certificates.Certificate9455

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporHN

open CFSG.Sporadic.HNSchreier

theorem hn_local : ∃ (z : JH) (R D : Subgroup JH),
      z ^ 3 = 1 ∧ z ≠ 1 ∧ z ∈ PJ ∧ (∀ q ∈ PJ, q * z = z * q) ∧
      CFSG.Assembly.IsElemAbelian 3 D ∧ 81 ≤ Nat.card D ∧
      R ≤ PJ ∧ Nat.card R * 3 = Nat.card PJ ∧
      ∀ s ∈ R, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ g : JH, g * s * g⁻¹ ∈ D ∧ g * z * g⁻¹ ∈ D :=
  Certificates.certificate9455

end CFSG.RankThree.PartTwo.Sec4.Item434SporHN
