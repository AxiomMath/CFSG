module

public import CFSG.Sporadic.Schreier.LyOuter

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.Ly CFSG.Blueprint CFSG.Sporadic.LySchreier
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

theorem card_outer_lyC_dvd' :
    Nat.card (Outer lyC) ∣ 2 :=
  (Subgroup.card_dvd_of_injective (centerQuotientOuterHom lyC)
    (centerQuotient_outer_injective lyC)).trans
    (outer_card_dvd_two_of_equiv_outside_six (Or.inr (by norm_num)) lyCenterEquiv)

theorem card_outer_J_dvd' :
    Nat.card (Outer J) ∣ 2 := by
  have h1 : Nat.card (Outer J) = autZToOuterJ.ker.index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 autZToOuterJ_surjective, Subgroup.card_top]
  have h2 : autZToOuterJ.ker.index ∣ autZToOuterC.ker.index :=
    Subgroup.index_dvd_of_le ker_autZToOuterC_le
  have h3 : autZToOuterC.ker.index = Nat.card autZToOuterC.range := Subgroup.index_ker _
  have h4 : Nat.card autZToOuterC.range ∣ Nat.card (Outer lyC) :=
    Subgroup.card_subgroup_dvd_card _
  rw [h1]
  exact h2.trans (h3 ▸ h4.trans card_outer_lyC_dvd')

theorem outer_order_divides_two'
    {T : Type*} [Group T] (hT : Nonempty (T ≃* NativeSporadic.Ly)) :
    Nat.card (Outer T) ∣ 2 ∧ (Nat.card (Outer T) = 1 ∨ Nat.card (Outer T) = 2) := by
  obtain ⟨e⟩ := hT
  have eq := CFSG.ComponentClassification.OuterAutomorphisms.equivalence (G := T) (H := J)
    (by exact e.trans lyEquivJ)
  have h : Nat.card (Outer T) ∣ 2 := by
    rw [Nat.card_congr eq.toEquiv]
    exact card_outer_J_dvd'
  exact ⟨h, (Nat.dvd_prime Nat.prime_two).1 h⟩

end CFSG.RankThree.PartOne.SPOR
