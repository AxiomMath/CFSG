module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate291100
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
  CFSG.RankThree.PartOne.MultRes
open scoped commutatorElement

theorem fi22_five_check :
    (ops3 77).squareCheck fi22MultFive = true :=
  Certificates.certificate291100

theorem Fi22_sylow5_square_witness :
    ∃ x y h : NativeSporadic.Fi22,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Fi22)) = 5 ^ 2 ∧
      h * x * h⁻¹ = x ^ 4 * y ^ 2 ∧ h * y * h⁻¹ = x ^ 2 * y ^ 4 :=
  (spec3 77).square_of_check fi22MultFive fi22_five_check

theorem sporadicKernelTrivial_fi22_five :
    SporadicKernelTrivial .Fi22 5 := by
  obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := Fi22_sylow5_square_witness
  have hcard : Nat.card (NativeSporadic.Carrier .Fi22) = 64561751654400 :=
    CFSG.Sporadic.Fi22.card_Fi22
  have : Finite (NativeSporadic.Carrier .Fi22) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_square Nat.prime_five hx hy hxy
    hQ (by rw [hcard]; decide) hhx hhy (by decide +revert))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
