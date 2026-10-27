module

public import CFSG.RankThree.PartTwo.Sec4.Item413Orders
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.RankThree.Asc83Table.M23
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint

theorem rankSporadic_of_J3
    (hJ3 : CFSG.pRank 3 (NativeSporadic.Carrier .J3 ⧸
      Subgroup.center (NativeSporadic.Carrier .J3)) ≤ 3) :
    ∀ s ∈ sporadics46, s ≠ .McL →
      CFSG.pRank 3 (NativeSporadic.Carrier s ⧸ Subgroup.center (NativeSporadic.Carrier s)) ≤ 3 := by
  intro s hs hsM
  simp only [sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change CFSG.pRank 3 (NativeSporadic.M11 ⧸ Subgroup.center NativeSporadic.M11) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num)
  · change CFSG.pRank 3 (NativeSporadic.M12 ⧸ Subgroup.center NativeSporadic.M12) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)
  · change CFSG.pRank 3 (NativeSporadic.M22 ⧸ Subgroup.center NativeSporadic.M22) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num)
  · change CFSG.pRank 3 (NativeSporadic.M23 ⧸ Subgroup.center NativeSporadic.M23) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.RankThree.Asc83Table.M23.card_M23]; norm_num)
  · change CFSG.pRank 3 (NativeSporadic.M24 ⧸ Subgroup.center NativeSporadic.M24) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)
  · change CFSG.pRank 3 (NativeSporadic.J1 ⧸ Subgroup.center NativeSporadic.J1) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.Sporadic.J1.card_J1]; norm_num)
  · change CFSG.pRank 3 (NativeSporadic.J2 ⧸ Subgroup.center NativeSporadic.J2) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.Sporadic.J2.card_J2]; norm_num)
  · exact hJ3
  · change CFSG.pRank 3 (NativeSporadic.J4 ⧸ Subgroup.center NativeSporadic.J4) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.Sporadic.J4.card_J4]; norm_num)
  · exact absurd rfl hsM
  · change CFSG.pRank 3 (NativeSporadic.HS ⧸ Subgroup.center NativeSporadic.HS) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.Sporadic.HS.card_HS]; norm_num)
  · change CFSG.pRank 3 (NativeSporadic.He ⧸ Subgroup.center NativeSporadic.He) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.Sporadic.He.card_He]; norm_num)
  · change CFSG.pRank 3 (NativeSporadic.Ru ⧸ Subgroup.center NativeSporadic.Ru) ≤ 3
    exact pRank_quotient_center_le_three (by rw [CFSG.Sporadic.Ru.card_Ru]; norm_num)

theorem rankTits_holds : ∀ (X : Type) [Group X] (f : ℕ), ReeTitsModel X .Tits 2 f →
    CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 3 := by
  intro X _ f h
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 f h
  have : Finite CFSG.Sporadic.Schreier.Tits.titsD :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Schreier.Tits.card_titsD]; norm_num)
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  refine pRank_quotient_center_le_three ?_
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  norm_num

end CFSG.RankThree.PartTwo.Sec4
