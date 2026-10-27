module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate14993
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
open scoped commutatorElement

theorem suz_mult_check :
    (ops3 64).squareCheck suzMultData = true :=
  Certificates.certificate14993

theorem Suz_sylow5_square_witness :
    ∃ x y h : NativeSporadic.Suz,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Suz)) = 5 ^ 2 ∧
      h * x * h⁻¹ = x ^ 3 * y ^ 0 ∧ h * y * h⁻¹ = x ^ 0 * y ^ 3 :=
  (spec3 64).square_of_check suzMultData suz_mult_check

theorem sporadicKernelTrivial_suz_five :
    SporadicKernelTrivial .Suz 5 := by
  obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := Suz_sylow5_square_witness
  have hcard : Nat.card (NativeSporadic.Carrier .Suz) = 448345497600 :=
    CFSG.Sporadic.Suz.card_Suz
  have : Finite (NativeSporadic.Carrier .Suz) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_square Nat.prime_five hx hy hxy
    hQ (by rw [hcard]; decide) hhx hhy (by decide +revert))

end CFSG.RankThree.PartOne.MultRes
