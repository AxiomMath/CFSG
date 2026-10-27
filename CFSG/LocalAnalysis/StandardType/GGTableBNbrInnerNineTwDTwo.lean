module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrConj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace TypeA

variable {K : Type} [Field K] [Finite K]

theorem card_lt_cube_pgl_two_of_card_four {p : ℕ} (hK : Nat.card K = 4) (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut (projectiveSL 2 K))} (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL 2 K))) ⊆ Set.range (conjAut 2 K)) :
    Nat.card X < p ^ 3 := by
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hGL : Nat.card (GL (Fin 2) K) = 180 := by
    rw [Matrix.card_GL_field, hq, Fin.prod_univ_two]
    norm_num
  have hle : X ≤ (conjAut 2 K).range := fun x hx => hXI hx
  have hdvd : Nat.card X ∣ 180 := by
    rw [← hGL]
    exact (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_range_dvd (conjAut 2 K))
  have := Fact.mk hp
  have : Finite X := Subtype.finite
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (TableB.isPGroup_of_isElemAbelian hX)
  rw [hk] at hdvd ⊢
  have hk3 : k < 3 := by
    by_contra hk3
    have h3 : 3 ≤ k := le_of_not_gt hk3
    have hdvd3 : p ^ 3 ∣ 180 := (pow_dvd_pow p h3).trans hdvd
    have hp5 : p ≤ 5 := by
      have hle3 : p ^ 3 ≤ 180 := Nat.le_of_dvd (by norm_num) hdvd3
      by_contra h5
      have h6 : 6 ≤ p := by omega
      have : 6 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left h6 3
      norm_num at this
      omega
    obtain ⟨m, rfl⟩ := hp.odd_of_ne_two hp2
    have hm : m = 1 ∨ m = 2 := by
      have h2 := hp.two_le
      omega
    rcases hm with rfl | rfl <;> norm_num at hdvd3
  exact Nat.pow_lt_pow_right hp.one_lt hk3

end TypeA

theorem recipeLinear_two_card_lt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear 2 4 Q) :
    LargeEvenRecipeLinear 2 4 fun R _ I F => Q R I F ∧ ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun X hXI hX => ?_⟩
  exact StdSubRestThree.card_lt_of_congr (TypeA.recipeEquiv 2 K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (fun _ hX'I hX' => TypeA.card_lt_cube_pgl_two_of_card_four hK hp hp2 hX' hX'I) hXI hX

theorem largeEvenLabelAll_card_lt_twDTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (h : lab.tag = .twD ∧ lab.rank = 2 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, rfl, rfl⟩ := h
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  exact recipeLinear_two_card_lt hp hp2 (by simpa using hQ)

theorem GGResHyp.false_of_twDTwo
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twD ∧ lab.rank = 2 ∧ lab.n = 1) p Bs K) :
    False := by
  refine hH.false_of_labelAll_card_lt (fun p lab hp hp2 hΛ hSel => ?_) hK
  exact (largeEvenLabelAll_card_lt_twDTwo hp hp2 hSel).mono fun _ _ _ _ hB _ _ => hB

end CFSG.StandardType

end
