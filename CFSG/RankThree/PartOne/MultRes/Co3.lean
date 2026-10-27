module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate14994
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
open scoped commutatorElement

theorem co3_mult_check :
    (ops2 22).cubicCheck co3MultData = true :=
  Certificates.certificate14994

theorem Co3_sylow5_cubic_witness :
    ∃ x y h : NativeSporadic.Co3,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Co3)) = 5 ^ 3 ∧
      h * x * h⁻¹ = x ^ 1 * y ^ 2 * ⁅x, y⁆ ^ 2 ∧
      h * y * h⁻¹ = x ^ 2 * y ^ 2 * ⁅x, y⁆ ^ 4 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 3 :=
  (spec2 22).cubic_of_check co3MultData co3_mult_check

theorem sporadicKernelTrivial_co3_five :
    SporadicKernelTrivial .Co3 5 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := Co3_sylow5_cubic_witness
  have hcard : Nat.card (NativeSporadic.Carrier .Co3) = 495766656000 :=
    CFSG.Sporadic.Schreier.Co3.card_Co3_of_perm
  have : Finite (NativeSporadic.Carrier .Co3) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_cubic Nat.prime_five hx hy hz hzx hzy
    hQ (by rw [hcard]; decide) hhx hhy hhz (by decide +revert))

end CFSG.RankThree.PartOne.MultRes
