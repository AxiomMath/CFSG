module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module

@[expose] def jordanD (n a : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => if j.val < a ∧ i.val = j.val + a then 1 else 0

private def w183JBlockIdx (a m : ℕ) {n : ℕ} (hn : n = a + a + m) (j : Fin n) :
    Fin a ⊕ (Fin a ⊕ Fin m) :=
  if h1 : (j : ℕ) < a then Sum.inl ⟨j, h1⟩ else
    if h2 : (j : ℕ) < a + a then Sum.inr (Sum.inl ⟨j - a, by omega⟩) else
      Sum.inr (Sum.inr ⟨j - (a + a), by have := j.isLt; omega⟩)

private theorem w183JBlockIdx_of_lt {a m n : ℕ} (hn : n = a + a + m) {j : Fin n}
    (h : (j : ℕ) < a) : w183JBlockIdx a m hn j = Sum.inl ⟨j, h⟩ := by
  rw [w183JBlockIdx, dite_eq_left h]

private theorem w183JBlockIdx_of_mid {a m n : ℕ} (hn : n = a + a + m) {j : Fin n}
    (h1 : a ≤ (j : ℕ)) (h2 : (j : ℕ) < a + a) :
    w183JBlockIdx a m hn j = Sum.inr (Sum.inl ⟨j - a, by omega⟩) := by
  rw [w183JBlockIdx, dite_eq_right (by omega), dite_eq_left h2]

private theorem w183JBlockIdx_of_ge {a m n : ℕ} (hn : n = a + a + m) {j : Fin n}
    (h : a + a ≤ (j : ℕ)) :
    w183JBlockIdx a m hn j = Sum.inr (Sum.inr ⟨j - (a + a), by have := j.isLt; omega⟩) := by
  rw [w183JBlockIdx, dite_eq_right (by omega), dite_eq_right (by omega)]

private theorem w183JBlockIdx_add {a m n : ℕ} (hn : n = a + a + m) {j : Fin n}
    (h : (j : ℕ) < a) :
    w183JBlockIdx a m hn ⟨(j : ℕ) + a, by omega⟩ = Sum.inr (Sum.inl ⟨j, h⟩) := by
  rw [w183JBlockIdx_of_mid hn (j := ⟨(j : ℕ) + a, by omega⟩)
    (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
  simp only [Sum.inr.injEq, Sum.inl.injEq]
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

private theorem w183JBlockIdx_injective {a m n : ℕ} (hn : n = a + a + m) :
    Function.Injective (w183JBlockIdx a m hn) := by
  intro x y hxy
  have hx := x.isLt
  have hy := y.isLt
  apply Fin.ext
  rcases lt_or_ge (x : ℕ) a with hx1 | hx1 <;> rcases lt_or_ge (y : ℕ) a with hy1 | hy1
  · rw [w183JBlockIdx_of_lt hn hx1, w183JBlockIdx_of_lt hn hy1] at hxy
    simpa using hxy
  · rcases lt_or_ge (y : ℕ) (a + a) with hy2 | hy2
    · rw [w183JBlockIdx_of_lt hn hx1, w183JBlockIdx_of_mid hn hy1 hy2] at hxy
      exact absurd hxy Sum.inl_ne_inr
    · rw [w183JBlockIdx_of_lt hn hx1, w183JBlockIdx_of_ge hn hy2] at hxy
      exact absurd hxy Sum.inl_ne_inr
  · rcases lt_or_ge (x : ℕ) (a + a) with hx2 | hx2
    · rw [w183JBlockIdx_of_mid hn hx1 hx2, w183JBlockIdx_of_lt hn hy1] at hxy
      exact absurd hxy.symm Sum.inl_ne_inr
    · rw [w183JBlockIdx_of_ge hn hx2, w183JBlockIdx_of_lt hn hy1] at hxy
      exact absurd hxy.symm Sum.inl_ne_inr
  · rcases lt_or_ge (x : ℕ) (a + a) with hx2 | hx2 <;>
      rcases lt_or_ge (y : ℕ) (a + a) with hy2 | hy2
    · rw [w183JBlockIdx_of_mid hn hx1 hx2, w183JBlockIdx_of_mid hn hy1 hy2] at hxy
      have := congrArg Fin.val (Sum.inl_injective (Sum.inr_injective hxy))
      simp only at this
      omega
    · rw [w183JBlockIdx_of_mid hn hx1 hx2, w183JBlockIdx_of_ge hn hy2] at hxy
      exact absurd (Sum.inr_injective hxy) Sum.inl_ne_inr
    · rw [w183JBlockIdx_of_ge hn hx2, w183JBlockIdx_of_mid hn hy1 hy2] at hxy
      exact absurd (Sum.inr_injective hxy).symm Sum.inl_ne_inr
    · rw [w183JBlockIdx_of_ge hn hx2, w183JBlockIdx_of_ge hn hy2] at hxy
      have := congrArg Fin.val (Sum.inr_injective (Sum.inr_injective hxy))
      simp only at this
      omega

theorem sq_zero_jordan {n : ℕ} (t : Matrix (Fin n) (Fin n) (ZMod 2)) (ht : t * t = 0) :
    ∃ (P : GL (Fin n) (ZMod 2)) (a : ℕ), 2 * a ≤ n ∧
      (↑P⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2)) * t * (↑P : Matrix (Fin n) (Fin n) (ZMod 2)) =
        jordanD n a := by
  classical
  set φ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) := t.mulVecLin with hφ
  have hφφ : ∀ x, φ (φ x) = 0 := fun x => by
    simp only [hφ, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ht, Matrix.zero_mulVec]
  set Ker := LinearMap.ker φ with hKer
  set I := LinearMap.range φ with hI
  have hIK : I ≤ Ker := by
    rintro _ ⟨x, rfl⟩
    exact hφφ x
  obtain ⟨W, hW⟩ := Ker.exists_isCompl
  obtain ⟨C₀, hC₀⟩ := I.exists_isCompl
  set C := C₀ ⊓ Ker with hC
  have hsup : I ⊔ C = Ker := by
    rw [hC, ← sup_inf_assoc_of_le C₀ hIK, hC₀.sup_eq_top, top_inf_eq]
  have hinf : I ⊓ C = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_left).trans hC₀.inf_eq_bot.le)
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := Submodule.finrank_add_eq_of_isCompl hW
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq I C
  rw [hsup, hinf, finrank_bot, add_zero] at h3
  rw [Module.finrank_fin_fun] at h1 h2
  rw [← hKer, ← hI] at h1
  set a := finrank (ZMod 2) I with ha
  set m := finrank (ZMod 2) C with hm
  have hn : n = a + a + m := by omega
  have hWl : finrank (ZMod 2) W = a := by omega
  let bW := Module.finBasisOfFinrankEq (ZMod 2) W hWl
  let bC := Module.finBasisOfFinrankEq (ZMod 2) C hm.symm
  let w : Fin a → (Fin n → ZMod 2) := fun i => (bW i : Fin n → ZMod 2)
  let v : Fin m → (Fin n → ZMod 2) := fun j => (bC j : Fin n → ZMod 2)
  let y : Fin a → (Fin n → ZMod 2) := fun i => φ (w i)
  have hw : LinearIndependent (ZMod 2) w := bW.linearIndependent.map' W.subtype W.ker_subtype
  have hv : LinearIndependent (ZMod 2) v := bC.linearIndependent.map' C.subtype C.ker_subtype
  have hspanw : Submodule.span (ZMod 2) (Set.range w) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (bW i).2)
  have hspanv : Submodule.span (ZMod 2) (Set.range v) ≤ C :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (bC i).2)
  have hspany : Submodule.span (ZMod 2) (Set.range y) ≤ I :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨w i, rfl⟩)
  have hy : LinearIndependent (ZMod 2) y := hw.map (hW.disjoint.symm.mono_left hspanw)
  have hyv : LinearIndependent (ZMod 2) (Sum.elim y v) :=
    hy.sum_type hv ((disjoint_iff.mpr hinf).mono hspany hspanv)
  have hspanyv : Submodule.span (ZMod 2) (Set.range (Sum.elim y v)) ≤ Ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s | s, rfl⟩
    · exact hIK ⟨w s, rfl⟩
    · exact (inf_le_right : C ≤ Ker) (bC s).2
  have hg : LinearIndependent (ZMod 2) (Sum.elim w (Sum.elim y v)) :=
    hw.sum_type hyv (hW.disjoint.symm.mono hspanw hspanyv)
  let f : Fin n → (Fin n → ZMod 2) :=
    fun j => Sum.elim w (Sum.elim y v) (w183JBlockIdx a m hn j)
  have hf : LinearIndependent (ZMod 2) f := hg.comp _ (w183JBlockIdx_injective hn)
  let P : Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.of fun i j => f j i
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hf
  have hact : ∀ j : Fin n,
      φ (f j) = if h : (j : ℕ) < a then f ⟨j + a, by omega⟩ else 0 := by
    intro j
    by_cases hj1 : (j : ℕ) < a
    · rw [dite_eq_left hj1]
      simp only [f, w183JBlockIdx_of_lt hn hj1, Sum.elim_inl]
      rw [w183JBlockIdx_add hn hj1]
      simp only [Sum.elim_inr, Sum.elim_inl, y]
    · rw [dite_eq_right hj1]
      by_cases hj2 : (j : ℕ) < a + a
      · simp only [f, w183JBlockIdx_of_mid hn (by omega) hj2, Sum.elim_inr, Sum.elim_inl]
        exact hφφ (w _)
      · simp only [f, w183JBlockIdx_of_ge hn (show a + a ≤ (j : ℕ) by omega), Sum.elim_inr]
        exact (inf_le_right : C ≤ Ker) (bC _).2
  have htP : t * P = P * jordanD n a := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have hL : ∑ t', t i t' * P t' j = φ (f j) i := by
      simp [φ, P, Matrix.mulVec, dotProduct]
    rw [hL, hact j]
    split_ifs with hj
    · rw [Finset.sum_eq_single ⟨j + a, by omega⟩]
      · rw [jordanD, Matrix.of_apply, ite_eq_left ⟨hj, rfl⟩, mul_one]
        rfl
      · intro t' _ ht'
        rw [jordanD, Matrix.of_apply, ite_eq_right, mul_zero]
        rintro ⟨-, h⟩
        exact ht' (Fin.ext h)
      · simp
    · simp only [Pi.zero_apply]
      symm
      refine Finset.sum_eq_zero fun t' _ => ?_
      rw [jordanD, Matrix.of_apply, ite_eq_right (fun h => hj h.1), mul_zero]
  refine ⟨hP.unit, a, by omega, ?_⟩
  have hPunit : (↑(hP.unit) : Matrix (Fin n) (Fin n) (ZMod 2)) = P := IsUnit.unit_spec hP
  have hQ : (↑((hP.unit)⁻¹) : Matrix (Fin n) (Fin n) (ZMod 2)) * P = 1 := by
    simpa [hPunit] using Units.inv_mul hP.unit
  rw [hPunit]
  calc (↑((hP.unit)⁻¹) : Matrix (Fin n) (Fin n) (ZMod 2)) * t * P
      = ((↑((hP.unit)⁻¹) : Matrix (Fin n) (Fin n) (ZMod 2)) * P) * jordanD n a := by
        rw [Matrix.mul_assoc, htP, Matrix.mul_assoc]
    _ = jordanD n a := by rw [hQ, one_mul]

end CFSG.LocalAnalysis.WeakClosure81
