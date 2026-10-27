module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCH
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

theorem s16t3_card_irr_quot_of_sum_three (helem : ∀ w : W, w * w = 1)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hcomm : commSub ⊤ L = ⊤)
    (hsum : SumOfNatShape L (⊤ : Subgroup W) (fixV L) 3)
    (htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom) :
    Nat.card {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) // XMod.IsIrr ↥L Y} = 3 ∨
      Nat.card {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) // XMod.IsIrr ↥L Y} = 7 := by
  have hQ : ∀ q : W ⧸ modFix L (⊤ : Subgroup W), q ^ 2 = 1 := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, pow_two, helem w, QuotientGroup.mk_one]
  obtain ⟨I, hnat, hS, hind, htop⟩ := s16t3_quot_summands hq hsum
  have hS' : ∀ i, XMod.IsIrr ↥(⊤ : Subgroup ↥L) (tilde L (⊤ : Subgroup W) (I i)) :=
    fun i => (s16t3_isIrr_top_iff _).2 (hS i)
  rw [← s16t3_card_irr_top (A := ↥L)]
  exact s16t3_card_irr_three_or_seven hQ (S := fun i => tilde L (⊤ : Subgroup W) (I i)) hS' htop
    (fun i => s16t3_isotypicOfLength_isoComp hS' hind htop (hS' i))
    (fun i => s16t3_card_end_eq_two_of_endUnits (hS' i)
      (s16t3_endUnitsTrivial_tilde hq (hnat i)))
    (fun i j => by
      rw [s16t3_card_iso_top, s16t3_card_iso_top]
      exact s16t3_card_iso_eq_of_trans hq htrans (hS i) (hS j))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
