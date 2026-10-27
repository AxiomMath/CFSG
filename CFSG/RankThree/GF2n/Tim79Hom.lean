module

public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.RankThree.GF2n.Tim79

open Matrix CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule

section Coordinates

variable {K : Type*} [Field K] (f : (Fin 2 → K) →+ (Fin 2 → K) →+ (Fin 2 → K))
  (hf : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v w : Fin 2 → K),
    f (g.1 *ᵥ v) (g.1 *ᵥ w) = g.1 *ᵥ f v w)

include hf

private theorem map_upper (t : K) (v w : Fin 2 → K) :
    f ![v 0 + t * v 1, v 1] ![w 0 + t * w 1, w 1] =
      ![(f v w) 0 + t * (f v w) 1, (f v w) 1] := by
  have h := hf (upperElt K t) v w
  rwa [show ((upperElt K t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v
      = ![v 0 + t * v 1, v 1] from upperElt_mulVec t v,
    show ((upperElt K t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w
      = ![w 0 + t * w 1, w 1] from upperElt_mulVec t w,
    show ((upperElt K t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (f v w)
      = ![(f v w) 0 + t * (f v w) 1, (f v w) 1] from upperElt_mulVec t _] at h

private theorem map_diag (c : Kˣ) (v w : Fin 2 → K) :
    f ![(c : K) * v 0, ((c⁻¹ : Kˣ) : K) * v 1] ![(c : K) * w 0, ((c⁻¹ : Kˣ) : K) * w 1] =
      ![(c : K) * (f v w) 0, ((c⁻¹ : Kˣ) : K) * (f v w) 1] := by
  have h := hf (diagElt c) v w
  rwa [show ((diagElt c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v
      = ![(c : K) * v 0, ((c⁻¹ : Kˣ) : K) * v 1] from diagElt_mulVec c v,
    show ((diagElt c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w
      = ![(c : K) * w 0, ((c⁻¹ : Kˣ) : K) * w 1] from diagElt_mulVec c w,
    show ((diagElt c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (f v w)
      = ![(c : K) * (f v w) 0, ((c⁻¹ : Kˣ) : K) * (f v w) 1] from diagElt_mulVec c _] at h

private theorem map_weyl [CharP K 2] (v w : Fin 2 → K) :
    f ![v 1, v 0] ![w 1, w 0] = ![(f v w) 1, (f v w) 0] := by
  have hm : ∀ u : Fin 2 → K,
      ((weylElt K : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u
        = ![u 1, u 0] := by
    intro u
    ext i
    fin_cases i <;> simp [coe_weylElt, mulVec, dotProduct, Fin.sum_univ_two]
  have h := hf (weylElt K) v w
  rwa [hm v, hm w, hm (f v w)] at h

end Coordinates

theorem equivariant_biadditive_eq_zero {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (f : (Fin 2 → K) →+ (Fin 2 → K) →+ (Fin 2 → K))
    (hf : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v w : Fin 2 → K),
      f (g.1 *ᵥ v) (g.1 *ᵥ w) = g.1 *ᵥ f v w) : f = 0 := by
  have hsplit : ∀ x y : K, (![x, y] : Fin 2 → K) = ![x, 0] + ![0, y] := by
    intro x y
    ext i
    fin_cases i <;> simp
  set α : K → K := fun l => (f ![l, 0] ![0, 1]) 1 with hα
  have S1 : ∀ l t x y : K, f ![l, 0] ![x + t * y, y] =
      ![(f ![l, 0] ![x, y]) 0 + t * (f ![l, 0] ![x, y]) 1, (f ![l, 0] ![x, y]) 1] := by
    intro l t x y
    simpa using map_upper f hf t ![l, 0] ![x, y]
  have S2 : ∀ l t : K, f ![l, 0] ![t, 0] = ![t * α l, 0] := by
    intro l t
    have h := S1 l t 0 1
    have e : (![0 + t * 1, 1] : Fin 2 → K) = ![t, 0] + ![0, 1] := by
      ext i
      fin_cases i <;> simp
    rw [e, map_add] at h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [AddMonoidHom.add_apply, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at h0 h1
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, hα]
      linear_combination h0
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
      linear_combination h1
  have S3 : ∀ l y : K, (f ![l, 0] ![0, y]) 1 = y * α l := by
    intro l y
    have h := S1 l 1 0 y
    have e : (![0 + 1 * y, y] : Fin 2 → K) = ![y, 0] + ![0, y] := by
      ext i
      fin_cases i <;> simp
    rw [e, map_add, S2] at h
    have h0 := congrFun h 0
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      one_mul] at h0
    linear_combination -h0
  have hαadd : ∀ l l' : K, α (l + l') = α l + α l' := by
    intro l l'
    have e : (![l + l', 0] : Fin 2 → K) = ![l, 0] + ![l', 0] := by
      ext i
      fin_cases i <;> simp
    simp only [hα]
    rw [e, map_add]
    simp
  have hαunit : ∀ u : K, u ≠ 0 → α u = α 1 := by
    intro u hu
    have h := map_diag f hf (Units.mk0 u hu) ![1, 0] ![1, 0]
    simp only [Units.val_mk0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      mul_one, mul_zero] at h
    rw [S2, S2] at h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero] at h0
    exact mul_left_cancel₀ hu (by linear_combination h0)
  obtain ⟨c, hc0, hc1⟩ : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun c _ => by
      by_cases h0 : c = 0
      · simp [h0]
      · simp [hcon c h0]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ] at h1
    have h2 : ({0, 1} : Set K).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    omega
  have hc1' : 1 + c ≠ 0 := fun h => hc1 (CharTwo.add_eq_zero.mp h).symm
  have hα1 : α 1 = 0 := by
    have h2 : α 1 = α c + α (1 + c) := by
      rw [← hαadd, add_comm 1 c, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [hαunit c hc0, hαunit (1 + c) hc1'] at h2
    exact left_eq_add.mp h2
  have hα0 : ∀ l, α l = 0 := by
    intro l
    by_cases hl : l = 0
    · have := hαadd 0 0
      rw [add_zero] at this
      rw [hl]
      exact left_eq_add.mp this
    · rw [hαunit l hl, hα1]
  set β : K → K → K := fun l y => (f ![l, 0] ![0, y]) 0 with hβdef
  have S8 : ∀ l x y : K, f ![l, 0] ![x, y] = ![β l y, 0] := by
    intro l x y
    rw [hsplit x y, map_add, S2]
    ext i
    fin_cases i
    · simp [hβdef, hα0]
    · simp [S3, hα0]
  have S9 : ∀ l a b : K, f ![0, l] ![a, b] = ![0, β l a] := by
    intro l a b
    have h := map_weyl f hf ![l, 0] ![b, a]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [S8] at h
    simpa using h
  have hβ : ∀ l t : K, β l t = 0 := by
    intro l t
    have h := map_upper f hf t ![0, l] ![0, 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zero_add,
      mul_one] at h
    have e : (![t * l, l] : Fin 2 → K) = ![t * l, 0] + ![0, l] := by
      ext i
      fin_cases i <;> simp
    rw [e, map_add, AddMonoidHom.add_apply, S8, S9, S9] at h
    have h1 := congrFun h 1
    simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
      add_zero, zero_add] at h1
    have h0 : β l 0 = 0 := by
      simp [hβdef, vec2_zero]
    rw [h0] at h1
    exact h1
  refine AddMonoidHom.ext fun v => AddMonoidHom.ext fun w => ?_
  have hv : v = ![v 0, 0] + ![0, v 1] := by
    ext i
    fin_cases i <;> simp
  have hw : w = ![w 0, w 1] := by
    ext i
    fin_cases i <;> simp
  rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, hv, map_add, AddMonoidHom.add_apply, hw,
    S8, S9, hβ, hβ]
  ext i
  fin_cases i <;> simp

end CFSG.RankThree.GF2n.Tim79
