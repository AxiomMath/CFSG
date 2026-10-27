module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate291110
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
  CFSG.RankThree.PartOne.MultRes
open scoped commutatorElement

theorem fi24_five_check :
    (ops3 781).squareCheck fi24MultFive = true :=
  Certificates.certificate291110

theorem Fi24prime_sylow5_square_witness :
    ∃ x y h : NativeSporadic.Fi24prime,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Fi24prime)) = 5 ^ 2 ∧
      h * x * h⁻¹ = x ^ 1 * y ^ 1 ∧ h * y * h⁻¹ = x ^ 0 * y ^ 4 :=
  (spec3 781).square_of_check fi24MultFive fi24_five_check

theorem sporadicKernelTrivial_fi24prime_five :
    SporadicKernelTrivial .Fi24Prime 5 := by
  obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := Fi24prime_sylow5_square_witness
  have hcard : Nat.card (NativeSporadic.Carrier .Fi24Prime) = 1255205709190661721292800 :=
    CFSG.Sporadic.Fi24.card_Fi24prime
  have : Finite (NativeSporadic.Carrier .Fi24Prime) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_square Nat.prime_five hx hy hxy
    hQ (by rw [hcard]; decide) hhx hhy (by decide +revert))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
