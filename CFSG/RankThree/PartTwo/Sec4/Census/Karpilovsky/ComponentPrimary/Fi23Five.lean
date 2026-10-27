module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate291101
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
  CFSG.RankThree.PartOne.MultRes
open scoped commutatorElement

theorem fi23_five_check :
    (ops3 253).squareCheck fi23MultFive = true :=
  Certificates.certificate291101

theorem Fi23_sylow5_square_witness :
    ∃ x y h : NativeSporadic.Fi23,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Fi23)) = 5 ^ 2 ∧
      h * x * h⁻¹ = x ^ 4 * y ^ 0 ∧ h * y * h⁻¹ = x ^ 0 * y ^ 1 :=
  (spec3 253).square_of_check fi23MultFive fi23_five_check

theorem sporadicKernelTrivial_fi23_five :
    SporadicKernelTrivial .Fi23 5 := by
  obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := Fi23_sylow5_square_witness
  have hcard : Nat.card (NativeSporadic.Carrier .Fi23) = 4089470473293004800 :=
    CFSG.Sporadic.Fi23.card_Fi23
  have : Finite (NativeSporadic.Carrier .Fi23) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_square Nat.prime_five hx hy hxy
    hQ (by rw [hcard]; decide) hhx hhy (by decide +revert))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
