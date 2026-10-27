module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate14992
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
open scoped commutatorElement

theorem th_five_mult_check :
    (ops2 248).cubicCheck thMultData5 = true :=
  Certificates.certificate14992.1

theorem Th_sylow5_cubic_witness :
    ∃ x y h : NativeSporadic.Th,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Th)) = 5 ^ 3 ∧
      h * x * h⁻¹ = x ^ 4 * y ^ 0 * ⁅x, y⁆ ^ 4 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 4 * ⁅x, y⁆ ^ 3 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 :=
  (spec2 248).cubic_of_check thMultData5 th_five_mult_check

theorem sporadicKernelTrivial_th_five :
    SporadicKernelTrivial .Th 5 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := Th_sylow5_cubic_witness
  have hcard : Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 :=
    CFSG.RankThree.OddKernel.card_Th_eq
  have : Finite (NativeSporadic.Carrier .Th) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_cubic Nat.prime_five hx hy hz hzx hzy
    hQ (by rw [hcard]; decide) hhx hhy hhz (by decide +revert))

theorem th_seven_mult_check :
    (ops2 248).squareCheck thMultData7 = true :=
  Certificates.certificate14992.2

theorem Th_sylow7_square_witness :
    ∃ x y h : NativeSporadic.Th,
      x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Th)) = 7 ^ 2 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 1 ∧ h * y * h⁻¹ = x ^ 3 * y ^ 5 :=
  (spec2 248).square_of_check thMultData7 th_seven_mult_check

theorem sporadicKernelTrivial_th_seven :
    SporadicKernelTrivial .Th 7 := by
  obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := Th_sylow7_square_witness
  have hcard : Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 :=
    CFSG.RankThree.OddKernel.card_Th_eq
  have : Finite (NativeSporadic.Carrier .Th) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_square Nat.prime_seven hx hy hxy
    hQ (by rw [hcard]; decide) hhx hhy (by decide +revert))

end CFSG.RankThree.PartOne.MultRes
