module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item812Res5

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434Kit
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

@[expose] def kCode : List ℕ :=
  [0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0,
    1, 1, 1, 0]

@[expose] def kCodeInv : List ℕ :=
  [0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0,
    1, 0, 1, 1]

set_option maxRecDepth 10000 in
theorem kPair_check : pairCheck (kCode, kCodeInv) = true := by
  decide

set_option maxRecDepth 10000 in
theorem kCode_conj : mul6 (mul6 kCode tCode) kCodeInv = vecCode 0 2 2 := by
  decide

@[expose] noncomputable def kH6 : H6 :=
  ofCode (kCode, kCodeInv) kPair_check


theorem kH6_conj : kH6 * Sec4.Item434SmallTwoIII.tH * kH6⁻¹ = vecElt zH ![0, 2, 2] := by
  apply mat6_injective
  rw [map_mul, map_mul, kH6, mat6_ofCode, mat6_ofCode_inv, mat6_tH, mat6_vecElt,
    ← dec6_mul6, ← dec6_mul6, kCode_conj]
  rfl

theorem kH6_conj_mem_baseA : kH6 * Sec4.Item434SmallTwoIII.tH * kH6⁻¹ ∈ baseA zH := by
  rw [kH6_conj]
  exact vecElt_mem_baseA wreathFacts_zH _

theorem card_wreathW_zH_eq_pow :
    Nat.card (wreathW zH tH) = 3 ^ (Nat.card H6).factorization 3 := by
  rw [card_wreathW_zH, factorization_card_H6]
  norm_num

end CFSG.RankThree.PartTwo.Sec8.Item812Res5
