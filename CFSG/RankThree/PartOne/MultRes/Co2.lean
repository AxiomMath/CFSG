module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate14991
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
open scoped commutatorElement

theorem co2_mult_check :
    (ops2 22).cubicCheck co2MultData = true :=
  Certificates.certificate14991

theorem Co2_sylow5_cubic_witness :
    ∃ x y h : NativeSporadic.Co2,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Co2)) = 5 ^ 3 ∧
      h * x * h⁻¹ = x ^ 3 * y ^ 3 * ⁅x, y⁆ ^ 3 ∧
      h * y * h⁻¹ = x ^ 4 * y ^ 1 * ⁅x, y⁆ ^ 2 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 :=
  (spec2 22).cubic_of_check co2MultData co2_mult_check

theorem sporadicKernelTrivial_co2_five :
    SporadicKernelTrivial .Co2 5 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := Co2_sylow5_cubic_witness
  have hcard : Nat.card (NativeSporadic.Carrier .Co2) = 42305421312000 :=
    CFSG.Sporadic.Co2Cert.natCard_Co2
  have : Finite (NativeSporadic.Carrier .Co2) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_cubic Nat.prime_five hx hy hz hzx hzy
    hQ (by rw [hcard]; decide) hhx hhy hhz (by decide +revert))

end CFSG.RankThree.PartOne.MultRes
