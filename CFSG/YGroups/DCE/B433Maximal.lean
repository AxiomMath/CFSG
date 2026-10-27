module

public import CFSG.YGroups.Y433.Bound
public import CFSG.YGroups.DCE.B433MaximalInputs
public import Certificates.Certificate9354

public section

namespace CFSG.YGroups.DCE.B433

open CFSG.YGroups.DCE.B433Native

theorem b433Vals_sum : ∑ l ∈ Finset.range 23, b433Vals[l]! = 1015970529280000 := by decide

theorem index_psi_ge
    (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) :
    1015970529280000 ≤ psi.range.index := by
  have := B433_finite_card_le.1
  have hcard := Subgroup.card_mul_index psi.range
  have hH := card_range_psi_le
  have hpos : 0 < Nat.card psi.range := Nat.card_pos
  by_contra hlt
  rw [not_le] at hlt
  have : Nat.card B433 < 4154781481226426191177580544000000 := by
    rw [← hcard]
    calc Nat.card psi.range * psi.range.index
        ≤ 4089470473293004800 * psi.range.index := Nat.mul_le_mul_right _ hH
      _ < 4089470473293004800 * 1015970529280000 :=
          Nat.mul_lt_mul_of_pos_left hlt (by norm_num)
      _ = 4154781481226426191177580544000000 := by norm_num
  omega

theorem psi_range_maximal
    (hG : 4154781481226426191177580544000000 ≤ Nat.card B433)
    (L : Subgroup B433) (hL : psi.range ≤ L) : L = psi.range ∨ L = ⊤ :=
  Certificates.certificate9354 hG L hL

end CFSG.YGroups.DCE.B433
