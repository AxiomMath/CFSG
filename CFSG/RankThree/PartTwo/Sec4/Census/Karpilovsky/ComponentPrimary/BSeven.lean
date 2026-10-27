module

public import CFSG.RankThree.PartOne.MultRes.Glue
public import Certificates.Certificate291120

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.RankThree.PartOne.Mult
  CFSG.RankThree.PartOne.MultRes
open scoped commutatorElement

theorem B_sylow7_square_witness :
    ∃ x y h : NativeSporadic.B,
      x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.B)) = 7 ^ 2 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 1 ∧ h * y * h⁻¹ = x ^ 3 * y ^ 5 :=
  Certificates.certificate291120

theorem card_B_seven :
    Nat.card NativeSporadic.B = 4154781481226426191177580544000000 := by
  rw [CFSG.Monster.Existence.card_nativeB]
  decide

theorem sporadicKernelTrivial_b_seven :
    SporadicKernelTrivial .B 7 := by
  obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := B_sylow7_square_witness
  have hcard : Nat.card (NativeSporadic.Carrier .B) = 4154781481226426191177580544000000 :=
    card_B_seven
  have : Finite (NativeSporadic.Carrier .B) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact sporadicKernelTrivial_of_carrier (kernelTrivial_of_square (by norm_num) hx hy hxy
    hQ (by rw [hcard]; decide) hhx hhy (by decide +revert))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
