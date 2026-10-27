module

public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem sl2_mul_self_of_comm {K : Type*} [Field K] [CharP K 2]
    {e d : SpecialLinearGroup (Fin 2) K} (he : e * e = 1) (he1 : e ≠ 1) (hc : d * e = e * d) :
    d * d = 1 := by
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have hneg : ∀ x : K, -x = x := fun x => CharTwo.neg_eq x
  obtain ⟨a, b, c, f, hE⟩ : ∃ a b c f : K, (e : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, f] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  obtain ⟨y1, y2, y3, y4, hD⟩ : ∃ y1 y2 y3 y4 : K,
      (d : Matrix (Fin 2) (Fin 2) K) = !![y1, y2; y3, y4] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdetE : a * f - b * c = 1 := by
    have := e.2
    rwa [hE, Matrix.det_fin_two_of] at this
  have hdetD : y1 * y4 - y2 * y3 = 1 := by
    have := d.2
    rwa [hD, Matrix.det_fin_two_of] at this
  have hEE : (e : Matrix (Fin 2) (Fin 2) K) * e = 1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) he
    simpa using this
  have hcc : (d : Matrix (Fin 2) (Fin 2) K) * e = e * d := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hc
    simpa using this
  rw [hE] at hEE hcc
  rw [hD] at hcc
  have e00 := congrFun (congrFun hEE 0) 0
  have e11 := congrFun (congrFun hEE 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  have h1 : a * (a + f) = 0 := by linear_combination (e00 - hdetE) + (a * f - b * c) * h2
  have h1' : f * (a + f) = 0 := by linear_combination (e11 - hdetE) + (a * f - b * c) * h2
  have hsum : a + f = 0 := by
    by_contra hne
    have ha0 := (mul_eq_zero.1 h1).resolve_right hne
    have hf0 := (mul_eq_zero.1 h1').resolve_right hne
    apply hne
    rw [ha0, hf0, add_zero]
  have hfa : f = a := by
    have : f = -a := eq_neg_of_add_eq_zero_right hsum
    rw [this, hneg]
  subst hfa
  have c01 := congrFun (congrFun hcc 0) 1
  have c10 := congrFun (congrFun hcc 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at c01 c10
  have hb : b * (y1 - y4) = 0 := by linear_combination c01
  have hc' : c * (y1 - y4) = 0 := by linear_combination -c10
  have hy : y1 = y4 := by
    by_cases hb0 : b = 0
    · by_cases hc0 : c = 0
      · exfalso
        apply he1
        have ha1 : f = 1 := by
          have hsq : (f - 1) ^ 2 = 0 := by
            rw [hb0, hc0] at e00
            linear_combination e00 - (f - 1) * h2
          have := pow_eq_zero_iff (two_ne_zero) |>.1 hsq
          linear_combination this
        apply Subtype.ext
        rw [hE, hb0, hc0, ha1]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      · have := (mul_eq_zero.1 hc').resolve_left hc0
        linear_combination this
    · have := (mul_eq_zero.1 hb).resolve_left hb0
      linear_combination this
  subst hy
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hdetD + (y2 * y3) * h2
  · linear_combination (y1 * y2) * h2
  · linear_combination (y1 * y3) * h2
  · linear_combination hdetD + (y2 * y3) * h2

section Facts

theorem sl2_isQuasisimple {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) K) :=
  CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le le_rfl h4

theorem sl2_lieModel {p f' : ℕ} (hp5 : 5 ≤ p) (hf' : 1 ≤ f') {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 2 ^ (p * f')) {G : Type} [Group G]
    (e : SpecialLinearGroup (Fin 2) K' ≃* G) :
    LieModel (G ⧸ Subgroup.center G) .PSL 2 2 (p * f') := by
  let e' : ProjectiveSpecialLinearGroup (Fin 2) K' ≃* G ⧸ Subgroup.center G :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hpf : 5 ≤ p * f' := by nlinarith
  have hbig : 8 ≤ 2 ^ (p * f') := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (p * f') := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hadm : StatedLieAdmissible .PSL 2 2 (p * f') := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  refine Or.inl ⟨by decide, ?_⟩
  refine CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e' ?_
  exact ⟨hadm, K', inferInstance, inferInstance, hK',
    ⟨projectiveSpecialLinearGroupEquivStatedProj 2 K'⟩⟩

theorem sl2_card_lt {K₀ K : Type} [Field K₀] [Finite K₀] [Field K] [Finite K]
    (h2 : 2 ≤ Nat.card K₀) (h : Nat.card K₀ < Nat.card K) :
    Nat.card (SpecialLinearGroup (Fin 2) K₀) < Nat.card (SpecialLinearGroup (Fin 2) K) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  set x := Nat.card K₀
  set y := Nat.card K
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hxy : x ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left h.le 2
  calc x * (x ^ 2 - 1) < y * (x ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right h (by omega)
    _ ≤ y * (y ^ 2 - 1) := Nat.mul_le_mul_left _ (by omega)

end Facts

end CFSG.RankThree.PartOne.TCX.Ree
