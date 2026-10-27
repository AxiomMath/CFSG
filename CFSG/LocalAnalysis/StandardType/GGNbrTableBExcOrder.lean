module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcAdjoint
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylGenAdjoint
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreExc
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestScalar
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEvenLabels
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeylTypes
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBOrderRestOn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover TableB TableBSymp NbrInnerRest

namespace NbrTableBExc

section Recipe

variable {K : Type} [Field K]

theorem ggTorusAutCardDvdSCr_E8 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusAutCardDvdSCr p 8 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K)
      696729600 := by
  have hdet := TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E8 (Nat.coprime_one_left p)
  have hV := TableBExc.card_torusPow_E8 (K := K) hp hpq
  have hT := IOneRest.ggExcToralRankInput_E7E8 (τ := .E8) (K := K) (Or.inr rfl) hp hp2 hpq
  have hN := ggTorusInducedCardElt_adjoint (τ := .E8) hp hp2 hpq hdet hV hT
    TableBExc.Three.cartan_symm_E8
  rw [NoOffExc.card_weyl_E8] at hN
  exact ggTorusAutCardDvdSCr_of_inducedCardElt hp hp2 (TableBExc.idImage_subset_inn_E8 K)
    (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (ggTorusWeylGenElt_of_mulEquiv (TableBExc.recipeEquiv .E8 K)
      (ExcWeylGen.ggTorusWeylGenElt_adjoint (τ := .E8) hp hp2 hpq hdet hV hT))
    (ggTorusInducedCardElt_of_mulEquiv (TableBExc.recipeEquiv .E8 K) hN)

theorem ggTorusAutCardDvdSCr_E7 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusAutCardDvdSCr p 7 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K)
      2903040 := by
  have hdet := TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E7
    ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hV := TableBExc.card_torusPow_E7 (K := K) hp hpq
  have hT := IOneRest.ggExcToralRankInput_E7E8 (τ := .E7) (K := K) (Or.inl rfl) hp hp2 hpq
  have hN := ggTorusInducedCardElt_adjoint (τ := .E7) hp hp2 hpq hdet hV hT
    TableBExc.Three.cartan_symm_E7
  rw [NoOffExc.card_weyl_E7] at hN
  exact ggTorusAutCardDvdSCr_of_inducedCardElt hp hp2 (TableBExc.idImage_subset_inn_E7 K)
    (TableBExc.center_recipeGroup_eq_bot .E7 K)
    (ggTorusWeylGenElt_of_mulEquiv (TableBExc.recipeEquiv .E7 K)
      (ExcWeylGen.ggTorusWeylGenElt_adjoint (τ := .E7) hp hp2 hpq hdet hV hT))
    (ggTorusInducedCardElt_of_mulEquiv (TableBExc.recipeEquiv .E7 K) hN)

theorem ggTorusAutCardDvdSCr_E6 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) :
    GGTorusAutCardDvdSCr p 6 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)
      51840 := by
  have hdet := TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E6
    ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
  have hV := TableBExc.card_torusPow_E6 (K := K) hp hp3 hpq
  have hT := TableBExc.ggExcToralRankInput_E6_of_ne_three (K := K) hp hp2 hp3 hpq
  have hN := ggTorusInducedCardElt_adjoint (τ := .E6) hp hp2 hpq hdet hV hT
    NoOffExc.cartan_symm_E6
  rw [NoOffExc.card_weyl_E6] at hN
  exact ggTorusAutCardDvdSCr_of_pow
    (ggTorusAutCardDvdSCr_of_inducedCardElt hp hp2
      (fun _ hφ => mem_range_conj_of_mem_recipeID_E6 hp hp3 hφ.1 hφ.2)
      (TableBExc.center_recipeGroup_eq_bot .E6 K)
      (ggTorusWeylGenElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
        (ExcWeylGen.ggTorusWeylGenElt_adjoint (τ := .E6) hp hp2 hpq hdet hV hT))
      (ggTorusInducedCardElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K) hN))

end Recipe

theorem recipeChevalleyExc_autCardDvd {τ : Tag} {n p N : ℕ}
    (hτ : (τ = .E6 ∧ p ≠ 3 ∧ N = 51840) ∨ (τ = .E7 ∧ N = 2903040) ∨ (τ = .E8 ∧ N = 696729600))
    (hn : 1 ≤ n) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley τ.cartan (2 ^ n) false Q) :
    LargeEvenRecipeChevalley τ.cartan (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusAutCardDvdSCr p r R I N := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  rcases hτ with ⟨rfl, hp3, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 6,
      TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq, ggTorusAutCardDvdSCr_E6 hp hp2 hp3 hpq⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 7,
      TableBExc.ggTorusLift_E7 hp hp2 hpq, ggTorusAutCardDvdSCr_E7 hp hp2 hpq⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 8,
      TableBExc.ggTorusLift_E8 hp hp2 hpq, ggTorusAutCardDvdSCr_E8 hp hp2 hpq⟩

end NbrTableBExc

open NbrTableBExc

theorem ggNbrTableBOrderRestInputOn_exc_holds :
    GGNbrTableBOrderRestInputOn fun p lab => ¬ lab.tag = .C ∧ ¬ lab.tag = .D ∧
      ¬ (lab.tag = .E6 ∧ p = 3) := by
  rintro p hp - ⟨tag, l, n⟩ N hlab ⟨hC, hD, hE6⟩ hsp hN Q hQ
  have hn : 1 ≤ n := hlab.1
  have hpn : p ∣ 2 ^ n - 1 := hsp.2.2
  rcases hN with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ht, rfl⟩
  · exact (hC ht).elim
  · exact (hD ht).elim
  · dsimp only at ht hE6
    subst ht
    exact recipeChevalleyExc_autCardDvd (τ := .E6) (Or.inl ⟨rfl, fun h => hE6 ⟨rfl, h⟩, rfl⟩)
      hn hp hpn hQ
  · dsimp only at ht
    subst ht
    exact recipeChevalleyExc_autCardDvd (τ := .E7) (Or.inr (Or.inl ⟨rfl, rfl⟩)) hn hp hpn hQ
  · dsimp only at ht
    subst ht
    exact recipeChevalleyExc_autCardDvd (τ := .E8) (Or.inr (Or.inr ⟨rfl, rfl⟩)) hn hp hpn hQ

end CFSG.StandardType

end
