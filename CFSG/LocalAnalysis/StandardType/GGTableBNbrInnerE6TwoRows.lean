module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSCr
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate1953
public import Certificates.Certificate1954
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThreeIrred
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoSevenIrred
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Even


theorem two_dvd_card_adjoint_E6 {K : Type} [Field K] [CharP K 2] :
    2 ∣ Nat.card (adjointGroup .E6 K) := by
  let x : adjointGroup .E6 K :=
    ⟨pinnedX .E6 K (Pi.single 0 1) 1, pinnedX_mem_adjointGroup _ _⟩
  have hx1 : x ≠ 1 := by
    intro h
    have h1 : pinnedX .E6 K (Pi.single 0 1) 1 = pinnedX .E6 K (Pi.single 0 1) 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h
    exact one_ne_zero (pinnedX_injective .E6 K _ h1)
  have hx2 : x ^ 2 = 1 := by
    refine Subtype.ext ?_
    change pinnedX .E6 K (Pi.single 0 1) 1 * pinnedX .E6 K (Pi.single 0 1) 1 = 1
    rw [← pinnedX_add, one_add_one_eq_two, CharTwo.two_eq_zero, pinnedX_zero]
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  rw [← hxo]
  exact orderOf_dvd_natCard x

end Even

section Rows


theorem largeEvenLabelAll_torusNbrSCr_e6_two_three {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusNbrSCr 3 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn1⟩ := h
  dsimp only at htag hn1
  subst htag
  subst hn1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa only [pow_one] using hK
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  exact ggTorusNbrSCr_of_scWeylIrred Nat.prime_three (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (fun φ hφ _ => TableBExc.E6Three.recipeID_subset_inn_E6_two hK hφ)
    (ggCenterPrime_recipe_E6_two hK2 Nat.prime_three)
    (ggSCWeylIrred_of_mulEquiv (TableBExc.recipeEquiv .E6 K) (ggSCWeylIrred_adjoint_E6_two hK2))

theorem largeEvenLabelAll_torusLift_nbrSCr_e6_two_three {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧ GGTorusNbrSCr 3 r R I :=
  (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_E6_two h)
    (largeEvenLabelAll_torusNbrSCr_e6_two_three h)).mono fun _ _ _ _ ⟨hl, hn⟩ => ⟨4, hl, hn⟩

theorem ggTableBNbrInnerInputOn_e6TwoThreeRow :
    GGTableBNbrInnerInputOn fun p lab => lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3 := by
  refine ggTableBNbrInnerInputOn_of_labelsSCr fun p lab _ _ ⟨ht, hn, hp3⟩ => ?_
  subst hp3
  exact largeEvenLabelAll_torusLift_nbrSCr_e6_two_three ⟨ht, hn⟩

theorem largeEvenLabelAll_torusLift_nbrSCr_e6_two_seven {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 7 r R ∧ GGTorusNbrSCr 7 r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn1⟩ := h
  dsimp only at htag hn1
  subst htag
  subst hn1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa only [pow_one] using hK
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, inferInstance, inferInstance, hK, hQ, 0, ?_, ?_⟩
  · refine TypeA.ggTorusLift_zero ?_
    change 2 ∣ Nat.card (TableBExc.RecipeGroup .E6 K)
    rw [Nat.card_congr (TableBExc.recipeEquiv .E6 K).toEquiv]
    exact two_dvd_card_adjoint_E6
  · exact ggTorusNbrSCr_of_scWeylIrred Nat.prime_seven (TableBExc.center_recipeGroup_eq_bot .E6 K)
      (fun φ hφ _ => TableBExc.E6Three.recipeID_subset_inn_E6_two hK hφ)
      (ggCenterPrime_recipe_E6_two hK2 Nat.prime_seven)
      (ggSCWeylIrred_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
        (ggSCWeylIrred_adjoint_E6_two_seven hK2 0))

theorem ggTableBNbrInnerInputOn_e6TwoSevenRow :
    GGTableBNbrInnerInputOn fun p lab => lab.tag = .E6 ∧ lab.n = 1 ∧ p = 7 := by
  refine ggTableBNbrInnerInputOn_of_labelsSCr fun p lab _ _ ⟨ht, hn, hp7⟩ => ?_
  subst hp7
  exact largeEvenLabelAll_torusLift_nbrSCr_e6_two_seven ⟨ht, hn⟩

end Rows

end CFSG.StandardType

end
