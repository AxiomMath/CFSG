module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
import Certificates.Kernel.Sp62.Glue899102

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
  CFSG.RankThree.PartTwo.Sec4.Item434Kit in
theorem certificate899102 : 
    (∃ p : H6, p * zH 0 * p⁻¹ = zH 1 ∧ p * zH 1 * p⁻¹ = zH 0 ∧ p * zH 2 * p⁻¹ = zH 2) ∧
    (∃ p : H6, p * zH 0 * p⁻¹ = zH 0 ∧ p * zH 1 * p⁻¹ = zH 2 ∧ p * zH 2 * p⁻¹ = zH 1) ∧
    Subgroup.centralizer (baseA zH : Set H6) = baseA zH ∧
    (∀ a < 3, ∀ b < 3, ∀ c < 3, ([a, b, c].filter (· != 0)).length = 2 →
      ∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c = g * (zH 0 * zH 1) * g⁻¹) ∧
    (∀ a < 3, ∀ b < 3, ∀ c < 3, ([a, b, c].filter (· != 0)).length = 3 →
      ∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c = g * (zH 0 * zH 1 * zH 2) * g⁻¹) := CFSG.KD.Sp62.gen899102_holds

end Certificates
