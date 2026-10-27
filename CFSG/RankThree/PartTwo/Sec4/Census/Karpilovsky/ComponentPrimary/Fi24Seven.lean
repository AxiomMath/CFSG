module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate291111
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
  CFSG.RankThree.PartOne.MultRes
open scoped commutatorElement

theorem fi24_seven_check :
    (ops3 781).cubicCheck fi24MultSeven = true :=
  Certificates.certificate291111

theorem Fi24prime_sylow7_cubic_witness :
    ∃ x y h : NativeSporadic.Fi24prime,
      x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Fi24prime)) = 7 ^ 3 ∧
      h * x * h⁻¹ = x ^ 1 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 4 * ⁅x, y⁆ ^ 6 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 4 :=
  (spec3 781).cubic_of_check fi24MultSeven fi24_seven_check

theorem sporadicKernelTrivial_fi24prime_seven :
    SporadicKernelTrivial .Fi24Prime 7 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := Fi24prime_sylow7_cubic_witness
  have hcard : Nat.card (NativeSporadic.Carrier .Fi24Prime) = 1255205709190661721292800 :=
    CFSG.Sporadic.Fi24.card_Fi24prime
  have : Finite (NativeSporadic.Carrier .Fi24Prime) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_cubic Nat.prime_seven hx hy hz hzx hzy
    hQ (by rw [hcard]; decide) hhx hhy hhz (by decide +revert))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
