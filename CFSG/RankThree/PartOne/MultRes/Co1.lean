module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate14996
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
open scoped commutatorElement

theorem co1_mult_check :
    (ops2 24).squareCheck co1MultData = true :=
  Certificates.certificate14996

theorem Co1_sylow7_square_witness :
    ∃ x y h : NativeSporadic.Co1,
      x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Co1)) = 7 ^ 2 ∧
      h * x * h⁻¹ = x ^ 3 * y ^ 5 ∧ h * y * h⁻¹ = x ^ 1 * y ^ 0 :=
  (spec2 24).square_of_check co1MultData co1_mult_check

theorem sporadicKernelTrivial_co1_seven :
    SporadicKernelTrivial .Co1 7 := by
  obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := Co1_sylow7_square_witness
  have hcard : Nat.card (NativeSporadic.Carrier .Co1) = 4157776806543360000 :=
    CFSG.Sporadic.Co1.card_Co1
  have : Finite (NativeSporadic.Carrier .Co1) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_square Nat.prime_seven hx hy hxy
    hQ (by rw [hcard]; decide) hhx hhy (by decide +revert))

end CFSG.RankThree.PartOne.MultRes
