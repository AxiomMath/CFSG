module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreElt
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.RankThree.CentralCover TableB TableBSymp
  NbrInnerRest

namespace CorFourTwoMore

section Exc

variable {K : Type} [Field K]

theorem ggTorusIrred_E8 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusIrred p 8 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) :=
  ggTorusIrred_of_irredSecElt hp (TableBExc.idImage_subset_inn_E8 K)
    (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (ggTorusIrredSecElt_of_reflElt hp hp2 (ggTorusReflElt_of_mulEquiv (TableBExc.recipeEquiv .E8 K)
      (ggTorusReflElt_adjoint (τ := .E8) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E8
          (Nat.coprime_one_left p))
        (cartanE_connected (by decide)) (fun i j h => cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E8 hp hpq)
        (IOneRest.ggExcToralRankInput_E7E8 (Or.inr rfl) hp hp2 hpq))))

theorem ggTorusIrred_E7 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusIrred p 7 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) :=
  ggTorusIrred_of_irredSecElt hp (TableBExc.idImage_subset_inn_E7 K)
    (TableBExc.center_recipeGroup_eq_bot .E7 K)
    (ggTorusIrredSecElt_of_reflElt hp hp2 (ggTorusReflElt_of_mulEquiv (TableBExc.recipeEquiv .E7 K)
      (ggTorusReflElt_adjoint (τ := .E7) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E7
          ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
        (cartanE_connected (by decide)) (fun i j h => cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E7 hp hpq)
        (IOneRest.ggExcToralRankInput_E7E8 (Or.inl rfl) hp hp2 hpq))))

theorem ggTorusIrred_E6 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusIrred p 6 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
  ggTorusIrred_of_pow (ggTorusIrred_of_irredSecElt hp
    (fun _ hφ => mem_range_conj_of_mem_recipeID_E6 hp hp3 hφ.1 hφ.2)
    (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (ggTorusIrredSecElt_of_reflElt hp hp2 (ggTorusReflElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
      (ggTorusReflElt_adjoint (τ := .E6) hp hpq
        (TableBExc.isUnit_det_cartan_of_eq hp CFSG.LieType.Chevalley.det_cartan_E6
          ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)))
        (cartanE_connected (by decide)) (fun i j h => cartanE_entry_ne_zero hp hp2 i j h)
        (TableBExc.card_torusPow_E6 hp hp3 hpq)
        (TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq)))))

theorem ggTorusIrred_F4 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusIrred p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
  ggTorusIrred_of_irredSecElt hp (TableBF4.idImage_subset_inn K)
    (TableBF4.center_recipeGroup_eq_bot K)
    (ggTorusIrredSecElt_of_reflElt hp hp2 (ggTorusReflElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ggTorusReflElt_adjointF4 hp hp2 hpq
        (ggF4ToralRankInput_of_three hp hp2 hpq fun _ => ggF4ThreeRankInput_holds))))

theorem recipeChevalleyExc_torusIrred {τ : Tag} {n p : ℕ}
    (hτ : (τ = .E6 ∧ p ≠ 3) ∨ τ = .E7 ∨ τ = .E8) (hn : 1 ≤ n) (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley τ.cartan (2 ^ n) false Q) :
    LargeEvenRecipeChevalley τ.cartan (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  rcases hτ with ⟨rfl, hp3⟩ | rfl | rfl
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 6,
      TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq, ggTorusIrred_E6 hp hp2 hp3 hpq⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 7,
      TableBExc.ggTorusLift_E7 hp hp2 hpq, ggTorusIrred_E7 hp hp2 hpq⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 8,
      TableBExc.ggTorusLift_E8 hp hp2 hpq, ggTorusIrred_E8 hp hp2 hpq⟩

theorem recipeChevalleyF4_torusIrred {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false Q) :
    LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 4, TableBF4.ggTorusLift_F4 hp hp2 hpq,
    ggTorusIrred_F4 hp hp2 hpq⟩

end Exc

end CorFourTwoMore

open CorFourTwoMore

section Labels


theorem largeEvenLabelAll_torusIrred_excSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBNbrInnerExcSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases htag with ⟨ht, hp3⟩ | ht | ht <;> dsimp only at ht hpn <;> subst ht
  · exact recipeChevalleyExc_torusIrred (τ := .E6) (Or.inl ⟨rfl, hp3⟩) hn hp hpn hQ
  · exact recipeChevalleyExc_torusIrred (τ := .E7) (Or.inr (Or.inl rfl)) hn hp hpn hQ
  · exact recipeChevalleyExc_torusIrred (τ := .E8) (Or.inr (Or.inr rfl)) hn hp hpn hQ

theorem ggTableBIrredInputOn_excSplit : GGTableBIrredInputOn GGTableBNbrInnerExcSplitLabel :=
  ggTableBIrredInputOn_of_labels fun _ _ hp hlab h =>
    largeEvenLabelAll_torusIrred_excSplit hp hlab h

theorem largeEvenLabelAll_torusIrred_F4 {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBF4Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  exact recipeChevalleyF4_torusIrred hlab.1 hp hpn hQ

theorem ggTableBIrredInputOn_F4 : GGTableBIrredInputOn GGTableBF4Label :=
  ggTableBIrredInputOn_of_labels fun _ _ hp hlab h => largeEvenLabelAll_torusIrred_F4 hp hlab h

end Labels

end CFSG.StandardType

end
