module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKInputs
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ComponentClassification.OuterAutomorphisms

private theorem card_outer_dvd_two_of_card_mulAut_le {G : Type} [Group G] [Finite G]
    (hc : Subgroup.center G = ⊥) (hle : Nat.card (MulAut G) ≤ 2 * Nat.card G) :
    Nat.card (Outer G) ∣ 2 := by
  have hfin : Finite (MulAut G) :=
    Finite.of_injective (fun α : MulAut G => (α : G → G)) DFunLike.coe_injective
  have hmul := (inner G).card_eq_card_quotient_mul_card_subgroup
  rw [CFSG.Sporadic.Schreier.card_inner_of_center_eq_bot hc] at hmul
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hQ : 0 < Nat.card (Outer G) := Nat.card_pos
  have h2 : Nat.card (Outer G) ≤ 2 := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    change Nat.card (MulAut G ⧸ inner G) * Nat.card G ≤ 2 * Nat.card G
    rw [← hmul]
    exact hle
  interval_cases h : Nat.card (Outer G) <;> simp

theorem s16kOutM22_holds :
    S16kOutM22 := by
  intro X _ _ hX
  obtain ⟨e⟩ := hX
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.M22) :=
    Finite.of_equiv X e.toEquiv
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact card_outer_dvd_two_of_card_mulAut_le CFSG.Sporadic.Schreier.m22_center_eq_bot'
    CFSG.Sporadic.Schreier.m22_mulAut_card

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
