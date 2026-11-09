module

public import CFSG.Sporadic.Schreier.LyCover
public import CFSG.Sporadic.Schreier.LyCoverPres

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native

@[expose] def carC [LySeed] (i : Fin 9) : lyC := FreeGroup.lift cC (carT i)

theorem coe_carC [LySeed] (i : Fin 9) : (carC i : J) = evalWord cStar (carWords i) := by
  rw [carC, carT, ← Subgroup.coe_subtype, map_evalWord, map_evalWord]
  exact evalWord_congr fun l _ => lift_cC_strongF _

theorem repM_carMat [LySeed] (i : Fin 9) : RepM (carMat csArr i) (carC i : J) := by
  rw [coe_carC]
  exact repM_evalWordM (fun k => (repM_csArr k).1) (fun k => (repM_csArr k).2) _

theorem repM_carFoldM [LySeed] (w : List (Fin 9)) :
    RepM (carFoldM (carMat csArr) w) ((w.map fun n => (carC n : J)).prod) := by
  suffices h : ∀ (X : Mat) (x : J), RepM X x →
      RepM (w.foldl (fun X n => mulM 5 111 X (carMat csArr n)) X)
        (x * (w.map fun n => (carC n : J)).prod) by
    simpa [carFoldM] using h _ _ repM_id
  induction w with
  | nil => intro X x hX; simpa using hX
  | cons n w ih =>
    intro X x hX
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih _ _ (hX.mul (repM_carMat n))

theorem eq_of_oneOrA [LySeed] {X : Mat} {x : J} (hX : RepM X x) (h : oneOrA X = true) :
    x = 1 ∨ x = lyz := by
  unfold oneOrA at h
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  rcases h with h | h
  · rw [h] at hX
    exact Or.inl (hX.unique repM_id)
  · rw [h] at hX
    exact Or.inr (hX.unique repM_matA)

theorem car_rels [LySeed] (h : carPresOK csArr = true) :
    (∀ i, ((carC i ^ 3 : lyC) : J) = 1 ∨ ((carC i ^ 3 : lyC) : J) = lyz) ∧
    (∀ i j, i < j → (((carC i * carC j) ^ 2 : lyC) : J) = 1 ∨
      (((carC i * carC j) ^ 2 : lyC) : J) = lyz) ∧
    (∀ k : Fin 2, ((carGenWords k).map fun n => (carC n : J)).prod = cStar k ∨
      ((carGenWords k).map fun n => (carC n : J)).prod = cStar k * lyz) ∧
    (((carC 0 * carC 1) ^ 2 : lyC) : J) = lyz := by
  unfold carPresOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt, beq_iff_eq] at h
  obtain ⟨⟨⟨h3, h2⟩, hu⟩, hz⟩ := h
  refine ⟨fun i => ?_, fun i j hij => ?_, fun k => ?_, ?_⟩
  rotate_left 3
  · have hp := (repM_carMat 0).mul (repM_carMat 1)
    have hr := hp.mul hp
    rw [hz] at hr
    simp only [sq, Subgroup.coe_mul]
    exact hr.unique repM_matA
  · have hr := ((repM_carMat i).mul (repM_carMat i)).mul (repM_carMat i)
    rw [Subgroup.coe_pow, pow_three, ← mul_assoc]
    exact eq_of_oneOrA hr (h3 i)
  · have hp := (repM_carMat i).mul (repM_carMat j)
    simp only [sq, Subgroup.coe_mul]
    rcases h2 i j with h | h
    · exact absurd hij (not_lt.2 h)
    · exact eq_of_oneOrA (hp.mul hp) h
  · have hk := (repM_csArr k).1
    rcases hu k with e | e
    · exact Or.inl ((repM_carFoldM _).unique (e ▸ hk))
    · refine Or.inr ((repM_carFoldM _).unique ?_)
      rw [e]
      exact hk.mul repM_matA

end CFSG.Sporadic.LySchreier
