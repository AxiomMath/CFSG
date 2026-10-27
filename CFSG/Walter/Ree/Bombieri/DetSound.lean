module

public import CFSG.Walter.Ree.Bombieri.PolyList

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

open F3P hiding X
open Polynomial

variable {R : Type*} [CommRing R] {ι : ZMod 3 →+* R} {r : R} {T : Tab}
  (hm : PE.IsMul ι r (mulT T))
include hm

theorem atomsF_spec {ρ : ℕ → F3P} (hρ : ∀ i, (ρ i).Valid) :
    (∀ j, (atomsF T ρ j).Valid) ∧
      (F3P.ev ι r ∘ atomsF T ρ) = Elim.atomsOf (F3P.ev ι r ∘ ρ) := by
  have key : ∀ j, ((Elim.atomDef j).evalM (mulT T) ρ fun _ => zero).Valid ∧
      F3P.ev ι r ((Elim.atomDef j).evalM (mulT T) ρ fun _ => zero) =
        Elim.atomsOf (F3P.ev ι r ∘ ρ) j := by
    intro j
    obtain ⟨h1, h2⟩ := PE.evalM_spec hm hρ (fun _ => valid_zero) (Elim.atomDef j)
    refine ⟨h1, h2.trans ?_⟩
    simp only [Elim.atomsOf]
    congr 1
    funext k
    simp [ev_zero]
  have hav : ∀ j < 7, (((List.range 7).map fun j =>
      (Elim.atomDef j).evalM (mulT T) ρ fun _ => zero).toArray.getD j zero) =
      (Elim.atomDef j).evalM (mulT T) ρ fun _ => zero := by
    intro j hj
    simp [hj]
  constructor
  · intro j
    simp only [atomsF]
    split_ifs with hj
    · rw [hav j hj]; exact (key j).1
    · exact valid_zero
  · funext j
    simp only [Function.comp_apply, atomsF]
    split_ifs with hj
    · rw [hav j hj]; exact (key j).2
    · rw [ev_zero]
      have : Elim.atomDef j = 0 := by
        rcases j with _ | _ | _ | _ | _ | _ | _ | j <;> first | omega | rfl
      simp [Elim.atomsOf, this]

omit [CommRing R] hm in
theorem mget_elimMat (ρ : ℕ → F3P) (i j : Fin 12) :
    mget (elimMat T ρ) i j = (Elim.ent i j).evalM (mulT T) ρ (atomsF T ρ) := by
  simp [mget, elimMat]

theorem elimMat_spec {ρ : ℕ → F3P} (hρ : ∀ i, (ρ i).Valid) :
    (∀ i j : Fin 12, (mget (elimMat T ρ) i j).Valid) ∧
      (Matrix.of fun i j : Fin 12 => F3P.ev ι r (mget (elimMat T ρ) i j)) =
        Elim.matOf (F3P.ev ι r ∘ ρ) := by
  obtain ⟨hα, hα'⟩ := atomsF_spec hm hρ
  constructor
  · intro i j
    rw [mget_elimMat]
    exact (PE.evalM_spec hm hρ hα _).1
  · ext i j
    rw [Matrix.of_apply, mget_elimMat, (PE.evalM_spec hm hρ hα _).2, Elim.matOf,
      Matrix.of_apply, hα']

omit [CommRing R] hm in
theorem valid_mget_normMat (A : Mat) (i j : ℕ) : (mget (normMat A) i j).Valid := by
  simp only [mget, normMat]
  by_cases hi : i < A.size
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, hi, getElem?_pos,
      Option.map_some, Option.getD_some]
    by_cases hj : j < (A[i]).size
    · simp [hj, valid_normalize]
    · simp [hj, valid_zero]
  · simp [hi, valid_zero]

theorem luEntry_spec {L U : Mat} (hL : ∀ i j, (mget L i j).Valid)
    (hU : ∀ i j, (mget U i j).Valid) (i j : ℕ) :
    F3P.ev ι r (luEntry T L U i j) =
      ∑ k : Fin 12, F3P.ev ι r (mget L i k) * F3P.ev ι r (mget U k j) := by
  have hall : AllValid ((List.range 12).map fun k => mulT T (mget L i k) (mget U k j)) := by
    intro a ha
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
    exact (hm _ _ (hL i k) (hU k j)).1
  rw [luEntry, (sumL_spec hall).2, List.map_map, Fin.sum_univ_eq_sum_range
    (fun k => F3P.ev ι r (mget L i k) * F3P.ev ι r (mget U k j)) 12, ← sum_map_range]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  exact (hm _ _ (hL i k) (hU k j)).2

theorem det_of_luCheck {A L U : Mat} (hL : ∀ i j, (mget L i j).Valid)
    (hU : ∀ i j, (mget U i j).Valid) (h : luCheck T A L U = true) :
    (Matrix.of fun i j : Fin 12 => F3P.ev ι r (mget A i j)).det =
      ∏ i : Fin 12, F3P.ev ι r (mget U i i) := by
  simp only [luCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  set L' : Matrix (Fin 12) (Fin 12) R := Matrix.of fun i j => F3P.ev ι r (mget L i j)
  set U' : Matrix (Fin 12) (Fin 12) R := Matrix.of fun i j => F3P.ev ι r (mget U i j)
  have hA : (Matrix.of fun i j : Fin 12 => F3P.ev ι r (mget A i j)) = L' * U' := by
    ext i j
    rw [Matrix.of_apply, (h i i.2 j j.2).1.1.1, luEntry_spec hm hL hU, Matrix.mul_apply]
    rfl
  have hLlow : L'.IsLowerTriangular := by
    intro i j hij
    have := (h i i.2 j j.2).1.2
    simp only [OrderDual.toDual_lt_toDual] at hij
    simp only [Fin.lt_def.mp hij, ite_true] at this
    simp only [L', Matrix.of_apply, beq_iff_eq] at this ⊢
    rw [this, ev_zero]
  have hUup : U'.IsUpperTriangular := by
    intro i j hij
    have := (h i i.2 j j.2).2
    simp only [id] at hij
    simp only [Fin.lt_def.mp hij, ite_true] at this
    simp only [U', Matrix.of_apply, beq_iff_eq] at this ⊢
    rw [this, ev_zero]
  have hdiag : ∀ i : Fin 12, L' i i = 1 := by
    intro i
    have := (h i i.2 i i.2).1.1.2
    simp only [ite_true] at this
    simp only [L', Matrix.of_apply, beq_iff_eq] at this ⊢
    rw [this, ev_one]
  rw [hA, Matrix.det_mul, Matrix.det_of_isLowerTriangular L' hLlow,
    Matrix.det_of_isUpperTriangular hUup]
  simp [hdiag, U']

theorem detAt_spec {ρ : ℕ → F3P} (hρ : ∀ i, (ρ i).Valid) {d : F3P}
    (h : detAt T ρ = some d) :
    d.Valid ∧ (Elim.matOf (F3P.ev ι r ∘ ρ)).det = F3P.ev ι r d := by
  simp only [detAt] at h
  split_ifs at h with hc
  obtain rfl := (Option.some.inj h).symm
  have hL := valid_mget_normMat (luDecomp T (elimMat T ρ)).1
  have hU := valid_mget_normMat (luDecomp T (elimMat T ρ)).2
  have hall : AllValid ((List.range 12).map fun i =>
      mget (normMat (luDecomp T (elimMat T ρ)).2) i i) := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact hU i i
  obtain ⟨hv, he⟩ := prodT_spec hm hall
  refine ⟨hv, ?_⟩
  rw [← (elimMat_spec hm hρ).2, det_of_luCheck hm hL hU hc, he, List.map_map,
    Fin.prod_univ_eq_prod_range (fun i => F3P.ev ι r (mget (normMat (luDecomp T
      (elimMat T ρ)).2) i i)) 12, ← prod_map_range]
  rfl

end Spec

end CFSG.Walter.Ree.Bombieri
