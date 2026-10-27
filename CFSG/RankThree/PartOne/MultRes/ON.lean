module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate14995
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
open scoped commutatorElement

theorem on_mult_check :
    (ops3 154).cubicCheck onMultData = true :=
  Certificates.certificate14995

theorem ON_sylow7_cubic_witness :
    ∃ x y h : NativeSporadic.ON,
      x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.ON)) = 7 ^ 3 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 6 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 1 * y ^ 0 * ⁅x, y⁆ ^ 4 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 :=
  (spec3 154).cubic_of_check onMultData on_mult_check

theorem sporadicKernelTrivial_on_seven :
    SporadicKernelTrivial .ONan 7 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := ON_sylow7_cubic_witness
  have hcard : Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.ONSchreier.fam_on_vector_schreier_order.2.2.2.2.2.1
  have : Finite (NativeSporadic.Carrier .ONan) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_cubic Nat.prime_seven hx hy hz hzx hzy
    hQ (by rw [hcard]; decide) hhx hhy hhz (by decide +revert))

end CFSG.RankThree.PartOne.MultRes
