module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestBasic
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestVac

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem recipeSymplecticTwo_card_lt_of_dvd {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic 2 (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic 2 (2 ^ n) false fun R _ I F => Q R I F ∧ ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun X hXI hX => ?_⟩
  have : Finite (LargeEvenSpGroup K 2) := Subtype.finite
  have : Finite (LargeEvenProj (LargeEvenSpGroup K 2)) :=
    Finite.of_equiv _ (TableBSymp.spProjEquivSp (K := K) (m := 2)).symm.toEquiv
  exact TableBExcSmallRest.card_lt_of_subset_inn TableBSymp.center_spProj_eq_bot
    (fun A hA => (TableBSymp.card_le_of_isElemAbelian_spProj hp hp2 (by rw [hK]; exact hpq)
      hA).trans_lt (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
    (fun φ hφ => TableBSymp.sp_I_subset_inn (hXI hφ)) hX

theorem largeEvenLabelAll_card_lt_symplecticTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .B ∨ lab.tag = .C)
    (hr : lab.rank = 2) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  by_cases hpq : p ∣ 2 ^ lab.n - 1
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hr hpq
    subst hr
    intro Q hQ
    rcases ht with rfl | rfl
    · exact recipeSymplecticTwo_card_lt_of_dvd hp hp2 hpq hQ
    · exact recipeSymplecticTwo_card_lt_of_dvd hp hp2 hpq hQ
  · refine largeEvenLabelAll_card_lt_symplectic_of_ord hp hp2 hlab ht fun j hj hj2 => ?_
    obtain rfl : j = 1 := by omega
    rwa [pow_one]

theorem not_largeEvenMarking_of_labelAll_card_lt {X : Type} [Group X] {p : ℕ}
    {S : LargeEvenLabel → Prop}
    (hall : ∀ lab, LargeEvenInLambda2 lab → S lab → LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → ∀ E : Subgroup (MulAut R),
        (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E → Nat.card E < p ^ 3) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => S lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  intro h
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_and_labelAll hall (fun _ _ _ _ _ _ hP => hP.1) h
  obtain ⟨R, _, I, _, hs, hna, _, ⟨-, E, hEI, hE, h3⟩, hlt⟩ := largeEvenRawDatum_exists hraw
  exact (hlt hs hna E hEI hE).not_ge h3

theorem ggInndiag_pRank_le_two_A1 {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => (lab.tag = .A ∧ lab.rank = 1) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) :=
  not_largeEvenMarking_of_labelAll_card_lt fun _ hlab h =>
    (largeEvenLabelAll_card_lt_linearTwo hp hp2 hlab (.inl h)).mono fun _ _ _ _ h' _ _ => h'

theorem ggInndiag_pRank_le_two_A2 {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => (lab.tag = .A ∧ lab.rank = 2) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) :=
  not_largeEvenMarking_of_labelAll_card_lt fun _ _ h =>
    (largeEvenLabelAll_card_lt_A2_all hp hp2 h.1 h.2).mono fun _ _ _ _ h' _ _ => h'

theorem ggInndiag_pRank_le_two_B2 {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ =>
      ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) :=
  not_largeEvenMarking_of_labelAll_card_lt fun _ hlab h =>
    (largeEvenLabelAll_card_lt_symplecticTwo hp hp2 hlab h.1 h.2).mono fun _ _ _ _ h' _ _ => h'

theorem ggInndiag_pRank_le_two_twA2 {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => (lab.tag = .twA ∧ lab.rank = 2) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) :=
  not_largeEvenMarking_of_labelAll_card_lt fun _ hlab h =>
    largeEvenLabelAll_card_lt_unitaryThree_all hp hp2 hlab h.1 h.2

theorem ggInndiag_pRank_le_two_twD2 {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => (lab.tag = .twD ∧ lab.rank = 2) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) :=
  not_largeEvenMarking_of_labelAll_card_lt fun _ hlab h =>
    (largeEvenLabelAll_card_lt_linearTwo hp hp2 hlab (.inr h)).mono fun _ _ _ _ h' _ _ => h'

theorem ggInndiag_pRank_le_two_B2der {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => lab.tag = .B2der ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  refine not_largeEvenMarking_of_labelAll_card_lt fun lab _ ht =>
    LargeEvenLabelAll.mono (fun _ _ _ _ h' _ _ => h') ?_
  by_cases hp3 : p = 3
  · exact largeEvenLabelAll_card_lt_b2derThree ⟨hp3, ht⟩
  · exact NbrInnerNine.largeEvenLabelAll_card_lt_b2der_ne_three hp hp2 hp3 ht

end CFSG.StandardType

end
