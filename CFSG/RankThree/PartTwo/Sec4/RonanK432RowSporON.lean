module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Single
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint

theorem listRow_of_single_class_card_81 {S : Type} [Group S] [Finite S]
    (hcl : ∀ a b : S, orderOf a = 3 → orderOf b = 3 → ∃ k : S, k * a * k⁻¹ = b)
    {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4) :
    ListRow S := by
  obtain ⟨hcomm, hexp⟩ := hE
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  obtain ⟨x0, hx0⟩ := exists_ne (1 : E)
  have hxE : (x0 : S) ∈ E := x0.2
  have hx1 : (x0 : S) ≠ 1 := fun h => hx0 (Subtype.ext h)
  have hx : orderOf (x0 : S) = 3 := orderOf_eq_prime (hexp _ hxE) hx1
  obtain ⟨y, hyE, hyn⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers (x0 : S) := by
    by_contra hno
    push Not at hno
    have hle : E ≤ Subgroup.zpowers (x0 : S) := fun y hy => hno y hy
    have hcard' := Subgroup.card_le_of_le hle
    rw [hcard, Nat.card_zpowers, hx] at hcard'
    norm_num at hcard'
  have hc : (x0 : S) * y = y * (x0 : S) :=
    congrArg Subtype.val (hcomm.is_comm.comm (⟨(x0 : S), hxE⟩ : E) ⟨y, hyE⟩)
  exact listRow_of_single_class hcl hx (hexp y hyE) hc hyn

theorem row_carrier_on :
    RowOf (NativeSporadic.Carrier .ONan) := by
  intro S _ _ _ _ ⟨e⟩
  haveI : Finite NativeSporadic.ON := CFSG.Sporadic.finite_carrier_of_ne_M .ONan (by decide)
  obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.ON_elementary_three_rank_four
  refine GoodRow.of_mulEquiv (S := NativeSporadic.ON) e.symm ⟨?_, ?_⟩
  · exact listRow_of_single_class_card_81
      (fun _ _ ha hb => CFSG.RankThree.Native.onThree_fusion ha hb) hE hcard
  · exact outerRow_of_not_three_dvd_outer inputs47Core_outON

end CFSG.RankThree.PartTwo.Sec4.RonanK432
