module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate14990
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
open scoped commutatorElement

theorem mcl_mult_check :
    (ops3 21).cubicCheck mclMultData = true :=
  Certificates.certificate14990

theorem McL_sylow5_cubic_witness :
    ∃ x y h : NativeSporadic.McL,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.McL)) = 5 ^ 3 ∧
      h * x * h⁻¹ = x ^ 1 * y ^ 2 * ⁅x, y⁆ ^ 3 ∧
      h * y * h⁻¹ = x ^ 1 * y ^ 3 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 :=
  (spec3 21).cubic_of_check mclMultData mcl_mult_check

theorem sporadicKernelTrivial_mcl_five :
    SporadicKernelTrivial .McL 5 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := McL_sylow5_cubic_witness
  have hcard : Nat.card (NativeSporadic.Carrier .McL) = 898128000 :=
    CFSG.Sporadic.McL.card_McL
  have : Finite (NativeSporadic.Carrier .McL) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_cubic Nat.prime_five hx hy hz hzx hzy
    hQ (by rw [hcard]; decide) hhx hhy hhz (by decide +revert))

end CFSG.RankThree.PartOne.MultRes
