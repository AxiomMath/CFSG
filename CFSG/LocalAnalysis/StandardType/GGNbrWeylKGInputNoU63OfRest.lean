module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylKGInputRest
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelInputs
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryDvd
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitFive
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylKGInputNoU63

public section

namespace CFSG.StandardType

theorem ggNbrKGE6ThreeDvd_holds
    : GGNbrKGE6ThreeDvd := by
  intro K _ _ _ h3
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hKf : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  rw [hKf] at h3
  exact ggTorusNoLineComp_of_ggTorusNoLine (ggTorusNoLine_of_noInvariantLineSCr Nat.prime_three
    (ggNoInvariantLineSCr_of_ggTableBModuleSCr (by norm_num)
      (ggE6DivModuleInput_of_model E6ThreeModel.e6ThreeModel_holds K f f.pos hKf h3)))

theorem ggNbrKGTwE6ThreeDvd_of_scWeylIrred
    (hKG : GGNbrKGTwE6ThreeSubSCWeylIrred)
    : GGNbrKGTwE6ThreeDvd := by
  intro K _ _ n hn hK hd
  have h3 : ¬ 3 ∣ 2 ^ n + 1 := by
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    intro h3'
    have h2 : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h3' hd
    have h2' : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
    rw [h2'] at h2
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by norm_num)
  exact ggTorusNoLineComp_of_ggTorusNoLine
    (ggTorusNoLine_of_scNoLine Nat.prime_three (TwE6Delta.center_recipeR_eq_bot hn hK)
      (fun φ hφ _ => TwE6Delta.recipeI_subset_inn_of_not_dvd hn hK h3 hφ)
      (TwE6Delta.ggCenterPrime_three_twE6 hn hK h3)
      (ggSCNoLine_of_scWeylIrred Nat.prime_three (hKG K n hn hK hd)))

theorem ggNbrKGTwE6AddLarge_holds
    : GGNbrKGTwE6AddLarge := by
  intro K _ _ n p hn hK hp hp5 hpn
  haveI : Fact p.Prime := ⟨hp⟩
  exact ggTorusNoLineComp_of_ggTorusNoLine (ggTorusNoLine_of_noInvariantLineSCr hp
    (TwE6TB.ggNoInvariantLineSCr_of_irredSCr hp (TwE6TB.ggTorusIrredSCr_of_modelSCr hp5
      (ggTwE6TorusModelInput_holds K n p hn hK hp hpn hp5))))

theorem ggNbrKGE7SmallAdd_of_scWeylIrred
    (hKG : GGNbrKGExcPlusSCWeylIrred)
    : GGNbrKGE7SmallAdd := by
  intro p hp35 K _ _ _ hpq
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by omega
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hKf : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  exact ggTorusNoLineComp_of_ggTorusNoLine
    (ggTorusNoLine_of_scNoLine hp (TableBExc.center_recipeGroup_eq_bot .E7 K)
      (fun φ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ)
      (ExcSplitL.ggCenterPrime_recipe_E7 (f := (f : ℕ)) f.pos hKf hp hp2)
      (ggSCNoLine_of_scWeylIrred hp (hKG K p hp35 hpq).1))

theorem ggNbrKGE8SmallAdd_of_scWeylIrred
    (hKG : GGNbrKGExcPlusSCWeylIrred)
    : GGNbrKGE8SmallAdd := by
  intro p hp35 K _ _ _ hpq
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by omega
  exact ggTorusNoLineComp_of_ggTorusNoLine
    (ggTorusNoLine_of_scNoLine hp (TableBExc.center_recipeGroup_eq_bot .E8 K)
      (fun φ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ)
      (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2)
      (ggSCNoLine_of_scWeylIrred hp (hKG K p hp35 hpq).2))

theorem ggNbrWeylKGInputNoU63_of_rest
    (hKGE : GGNbrKGExcPlusSCWeylIrred)
    (hKGTw : GGNbrKGTwE6ThreeSubSCWeylIrred)
    (h : GGNbrWeylKGInputRest)
    : GGNbrWeylKGInputNoU63 := ⟨ggNbrKGE6ThreeDvd_holds, ggNbrKGTwE6ThreeDvd_of_scWeylIrred hKGTw, ggNbrKGTwE6AddLarge_holds,
    ggNbrKGE7SmallAdd_of_scWeylIrred hKGE, ggNbrKGE8SmallAdd_of_scWeylIrred hKGE, h.1, h.2.1,
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩

end CFSG.StandardType
