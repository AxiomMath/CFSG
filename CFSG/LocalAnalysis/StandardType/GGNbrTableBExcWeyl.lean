module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcAdjoint
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylGenAdjoint
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreExc
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestScalar
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEvenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBWeylOn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover TableB TableBSymp NbrInnerRest

namespace NbrTableBExc

section Recipe

variable {K : Type} [Field K]

theorem ggTorusReflGenW_E8 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusReflGenW p 8 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have hdet := TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E8 (Nat.coprime_one_left p)
  have hV := TableBExc.card_torusPow_E8 (K := K) hp hpq
  have hT := IOneRest.ggExcToralRankInput_E7E8 (τ := .E8) (K := K) (Or.inr rfl) hp hp2 hpq
  exact ggTorusReflGenW_of_inducedReflElt hp hp2 (TableBExc.idImage_subset_inn_E8 K)
    (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (ggTorusWeylGenElt_of_mulEquiv (TableBExc.recipeEquiv .E8 K)
      (ExcWeylGen.ggTorusWeylGenElt_adjoint (τ := .E8) hp hp2 hpq hdet hV hT))
    (ggTorusInducedReflElt_of_mulEquiv (TableBExc.recipeEquiv .E8 K)
      (ggTorusInducedReflElt_adjoint (τ := .E8) hp hp2 hpq hdet hV hT))

theorem ggTorusReflGenW_E7 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusReflGenW p 7 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  have hdet := TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E7
    ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hV := TableBExc.card_torusPow_E7 (K := K) hp hpq
  have hT := IOneRest.ggExcToralRankInput_E7E8 (τ := .E7) (K := K) (Or.inl rfl) hp hp2 hpq
  exact ggTorusReflGenW_of_inducedReflElt hp hp2 (TableBExc.idImage_subset_inn_E7 K)
    (TableBExc.center_recipeGroup_eq_bot .E7 K)
    (ggTorusWeylGenElt_of_mulEquiv (TableBExc.recipeEquiv .E7 K)
      (ExcWeylGen.ggTorusWeylGenElt_adjoint (τ := .E7) hp hp2 hpq hdet hV hT))
    (ggTorusInducedReflElt_of_mulEquiv (TableBExc.recipeEquiv .E7 K)
      (ggTorusInducedReflElt_adjoint (τ := .E7) hp hp2 hpq hdet hV hT))

theorem ggTorusReflGenW_E6 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) :
    GGTorusReflGenW p 6 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have hdet := TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E6
    ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
  have hV := TableBExc.card_torusPow_E6 (K := K) hp hp3 hpq
  have hT := TableBExc.ggExcToralRankInput_E6_of_ne_three (K := K) hp hp2 hp3 hpq
  exact ggTorusReflGenW_of_pow
    (ggTorusReflGenW_of_inducedReflElt hp hp2
      (fun _ hφ => mem_range_conj_of_mem_recipeID_E6 hp hp3 hφ.1 hφ.2)
      (TableBExc.center_recipeGroup_eq_bot .E6 K)
      (ggTorusWeylGenElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
        (ExcWeylGen.ggTorusWeylGenElt_adjoint (τ := .E6) hp hp2 hpq hdet hV hT))
      (ggTorusInducedReflElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
        (ggTorusInducedReflElt_adjoint (τ := .E6) hp hp2 hpq hdet hV hT)))

theorem ggTorusReflGenW_F4 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusReflGenW p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  have hT := ggF4ToralRankInput_of_three (K := K) hp hp2 hpq fun _ => ggF4ThreeRankInput_holds
  exact ggTorusReflGenW_of_inducedReflElt hp hp2 (TableBF4.idImage_subset_inn K)
    (TableBF4.center_recipeGroup_eq_bot K)
    (ggTorusWeylGenElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ExcWeylGen.ggTorusWeylGenElt_adjointF4 hp hp2 hpq hT))
    (ggTorusInducedReflElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ggTorusInducedReflElt_adjoint (τ := .F4) hp hp2 hpq
        (by rw [det_cartan_F4, Int.cast_one]; exact isUnit_one)
        (TableBF4.card_torusPow hp hpq) hT))

end Recipe

theorem recipeChevalleyExc_reflGenW {τ : Tag} {n p : ℕ}
    (hτ : (τ = .E6 ∧ p ≠ 3) ∨ τ = .E7 ∨ τ = .E8) (hn : 1 ≤ n) (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley τ.cartan (2 ^ n) false Q) :
    LargeEvenRecipeChevalley τ.cartan (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  rcases hτ with ⟨rfl, hp3⟩ | rfl | rfl
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 6,
      TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq, ggTorusReflGenW_E6 hp hp2 hp3 hpq⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 7,
      TableBExc.ggTorusLift_E7 hp hp2 hpq, ggTorusReflGenW_E7 hp hp2 hpq⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 8,
      TableBExc.ggTorusLift_E8 hp hp2 hpq, ggTorusReflGenW_E8 hp hp2 hpq⟩

theorem recipeChevalleyF4_reflGenW {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false Q) :
    LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 4, TableBF4.ggTorusLift_F4 hp hp2 hpq,
    ggTorusReflGenW_F4 hp hp2 hpq⟩

theorem largeEvenLabelAll_reflGenW_excSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBNbrInnerExcSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases htag with ⟨ht, hp3⟩ | ht | ht <;> dsimp only at ht hpn <;> subst ht
  · exact recipeChevalleyExc_reflGenW (τ := .E6) (Or.inl ⟨rfl, hp3⟩) hn hp hpn hQ
  · exact recipeChevalleyExc_reflGenW (τ := .E7) (Or.inr (Or.inl rfl)) hn hp hpn hQ
  · exact recipeChevalleyExc_reflGenW (τ := .E8) (Or.inr (Or.inr rfl)) hn hp hpn hQ

theorem largeEvenLabelAll_reflGenW_F4 {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBF4Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  exact recipeChevalleyF4_reflGenW hlab.1 hp hpn hQ

theorem largeEvenLabelAll_reflGenW_G2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .G2)
    (hsp : GGNbrSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  have hX := TableBExc.largeEvenLabelAll_card_lt_G2 hp hlab ht (Or.inl ⟨hsp.1, hsp.2.2⟩)
  have hpn := hsp.2.2
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hpn
  subst ht
  intro Q hQ
  have hQ' := hX Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq', hcard⟩ := hQ'
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, i1, i2, hK, hq', _,
    TableBF4.ggTorusLift_of_mulEquiv (TableBExc.recipeEquiv .G2 K)
      (TableBExc.ggTorusLift_adjoint (τ := .G2) (by decide) hp hp2 hpq
        (TableBExc.isUnit_det_cartan_of_eq hp det_cartan_G2 (Nat.coprime_one_left p))),
    ggTorusReflGenW_of_card_lt hcard⟩

end NbrTableBExc

open NbrTableBExc

theorem ggNbrTableBWeylInputOn_exc_holds :
    GGNbrTableBWeylInputOn fun p lab => ¬ lab.tag = .A ∧ ¬ lab.tag = .B ∧ ¬ lab.tag = .C ∧
      ¬ lab.tag = .D ∧ ¬ (lab.tag = .E6 ∧ p = 3) := by
  rintro p hp hp2 ⟨tag, l, n⟩ hlab ⟨hA, hB, hC, hD, hE6⟩ - hsp
  have hpn : p ∣ 2 ^ n - 1 := hsp.2.2
  cases tag with
  | A => exact (hA rfl).elim
  | B => exact (hB rfl).elim
  | C => exact (hC rfl).elim
  | D => exact (hD rfl).elim
  | E6 =>
    exact largeEvenLabelAll_reflGenW_excSplit hp hlab
      ⟨Or.inl ⟨rfl, fun h => hE6 ⟨rfl, h⟩⟩, hpn⟩
  | E7 => exact largeEvenLabelAll_reflGenW_excSplit hp hlab ⟨Or.inr (Or.inl rfl), hpn⟩
  | E8 => exact largeEvenLabelAll_reflGenW_excSplit hp hlab ⟨Or.inr (Or.inr rfl), hpn⟩
  | F4 => exact largeEvenLabelAll_reflGenW_F4 hp hlab ⟨rfl, hpn⟩
  | G2 => exact largeEvenLabelAll_reflGenW_G2 hp hp2 hlab rfl hsp
  | twA | twD | twE6 | triD4 | twB2 | twF4 | twF4der => exact False.elim hsp.1
  | B2der | G2der =>
    have h1 : n = 1 := by
      obtain ⟨-, -, h⟩ := hlab
      exact h
    have h2 : 2 ≤ n := hsp.2.1
    omega

end CFSG.StandardType

end
