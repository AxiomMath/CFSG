module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec4

namespace Item424Res5

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def blockBasis {A B : V →ₗ[K] V} {u w : V}
    (hli : LinearIndependent K ![u, A u, w, B w]) (hV : Module.finrank K V = 4) :
    Module.Basis (Fin 4) K V :=
  basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV])

theorem coe_blockBasis {A B : V →ₗ[K] V} {u w : V} (hli : LinearIndependent K ![u, A u, w, B w])
    (hV : Module.finrank K V = 4) : ⇑(blockBasis hli hV) = ![u, A u, w, B w] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

noncomputable def blockWeyl {A B : V →ₗ[K] V} {u w : V}
    (hli : LinearIndependent K ![u, A u, w, B w]) (hV : Module.finrank K V = 4) (s t : K) :
    V →ₗ[K] V :=
  (blockBasis hli hV).constr K ![w, B w, s • u + t • A u, (t - s) • u - s • A u]

section Values

variable {A B : V →ₗ[K] V} {u w : V} (hli : LinearIndependent K ![u, A u, w, B w])
  (hV : Module.finrank K V = 4) (s t : K)

theorem blockWeyl_u : blockWeyl hli hV s t u = w := by
  have h := (blockBasis hli hV).constr_basis K ![w, B w, s • u + t • A u, (t - s) • u - s • A u] 0
  rw [coe_blockBasis] at h
  exact h

theorem blockWeyl_Au : blockWeyl hli hV s t (A u) = B w := by
  have h := (blockBasis hli hV).constr_basis K ![w, B w, s • u + t • A u, (t - s) • u - s • A u] 1
  rw [coe_blockBasis] at h
  exact h

theorem blockWeyl_w : blockWeyl hli hV s t w = s • u + t • A u := by
  have h := (blockBasis hli hV).constr_basis K ![w, B w, s • u + t • A u, (t - s) • u - s • A u] 2
  rw [coe_blockBasis] at h
  exact h

theorem blockWeyl_Bw : blockWeyl hli hV s t (B w) = (t - s) • u - s • A u := by
  have h := (blockBasis hli hV).constr_basis K ![w, B w, s • u + t • A u, (t - s) • u - s • A u] 3
  rw [coe_blockBasis] at h
  exact h

end Values

section Relations

variable {A B : V →ₗ[K] V} {u w : V} (hli : LinearIndependent K ![u, A u, w, B w])
  (hV : Module.finrank K V = 4) (s t : K)
  (hAA : u + A u + A (A u) = 0) (hAw : A w = w) (hABw : A (B w) = B w)
  (hBu : B u = u) (hBAu : B (A u) = A u) (hBB : w + B w + B (B w) = 0)

include hAA hAw hABw hBu hBAu hBB in
theorem blockWeyl_comp_A : blockWeyl hli hV s t ∘ₗ A = B ∘ₗ blockWeyl hli hV s t := by
  have hAA' : A (A u) = -u - A u := by rw [← sub_eq_zero]; rw [← hAA]; abel
  have hBB' : B (B w) = -w - B w := by rw [← sub_eq_zero]; rw [← hBB]; abel
  refine (blockBasis hli hV).ext fun i => ?_
  rw [coe_blockBasis]
  fin_cases i
  · simp [blockWeyl_u, blockWeyl_Au]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, LinearMap.coe_comp,
      Function.comp_apply]
    rw [hAA', map_sub, map_neg, blockWeyl_u, blockWeyl_Au, hBB']
  · simp only [Fin.reduceFinMk, Matrix.cons_val, LinearMap.coe_comp, Function.comp_apply]
    rw [hAw, blockWeyl_w, map_add, map_smul, map_smul, hBu, hBAu]
  · simp only [Fin.reduceFinMk, Matrix.cons_val, LinearMap.coe_comp, Function.comp_apply]
    rw [hABw, blockWeyl_Bw, map_sub, map_smul, map_smul, hBu, hBAu]

include hAA hAw hABw hBu hBAu hBB in
theorem blockWeyl_comp_B :
    blockWeyl hli hV s t ∘ₗ B = A ∘ₗ A ∘ₗ blockWeyl hli hV s t := by
  have hAA' : A (A u) = -u - A u := by rw [← sub_eq_zero]; rw [← hAA]; abel
  have hBB' : B (B w) = -w - B w := by rw [← sub_eq_zero]; rw [← hBB]; abel
  refine (blockBasis hli hV).ext fun i => ?_
  rw [coe_blockBasis]
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, LinearMap.coe_comp, Function.comp_apply]
    rw [hBu, blockWeyl_u, hAw, hAw]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, LinearMap.coe_comp,
      Function.comp_apply]
    rw [hBAu, blockWeyl_Au, hABw, hABw]
  · simp only [Fin.reduceFinMk, Matrix.cons_val, LinearMap.coe_comp, Function.comp_apply]
    rw [blockWeyl_Bw, blockWeyl_w]
    simp only [map_add, map_sub, map_neg, map_smul, hAA']
    module
  · simp only [Fin.reduceFinMk, Matrix.cons_val, LinearMap.coe_comp, Function.comp_apply]
    rw [hBB', map_sub, map_neg, blockWeyl_w, blockWeyl_Bw]
    simp only [map_sub, map_neg, map_smul, hAA']
    module

end Relations

section Det

variable {A B : V →ₗ[K] V} {u w : V} (hli : LinearIndependent K ![u, A u, w, B w])
  (hV : Module.finrank K V = 4) (s t : K)

theorem toMatrix_blockWeyl :
    LinearMap.toMatrix (blockBasis hli hV) (blockBasis hli hV) (blockWeyl hli hV s t) =
      !![0, 0, s, t - s; 0, 0, t, -s; 1, 0, 0, 0; 0, 1, 0, 0] := by
  set bs := blockBasis hli hV with hbs
  have hb : ∀ i, bs i = ![u, A u, w, B w] i := fun i => by rw [hbs, coe_blockBasis]
  have hv0 : bs.repr u = Finsupp.single 0 1 := by rw [← bs.repr_self 0, hb]; rfl
  have hv1 : bs.repr (A u) = Finsupp.single 1 1 := by rw [← bs.repr_self 1, hb]; rfl
  have hv2 : bs.repr w = Finsupp.single 2 1 := by rw [← bs.repr_self 2, hb]; rfl
  have hv3 : bs.repr (B w) = Finsupp.single 3 1 := by rw [← bs.repr_self 3, hb]; rfl
  ext i j
  rw [LinearMap.toMatrix_apply, hb]
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [blockWeyl_u, hv2]
    fin_cases i <;> simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [blockWeyl_Au, hv3]
    fin_cases i <;> simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [blockWeyl_w, map_add, map_smul, map_smul, hv0, hv1]
    fin_cases i <;> simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [blockWeyl_Bw, map_sub, map_smul, map_smul, hv0, hv1]
    fin_cases i <;> simp

theorem det_blockWeyl : LinearMap.det (blockWeyl hli hV s t) = -(s ^ 2 - s * t + t ^ 2) := by
  rw [← LinearMap.det_toMatrix (blockBasis hli hV), toMatrix_blockWeyl]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

end Det

section Isometry

variable {A B : V →ₗ[K] V} {u w : V} (hli : LinearIndependent K ![u, A u, w, B w])
  (hV : Module.finrank K V = 4) {s t : K}

theorem blockWeyl_isometry (ω : LinearMap.BilinForm K V) (hω : ω.IsAlt) (huA : ω u (A u) = 1)
    (hwB : ω w (B w) = 1) (huw : ω u w = 0) (huBw : ω u (B w) = 0) (hAuw : ω (A u) w = 0)
    (hAuBw : ω (A u) (B w) = 0)
    (hst : s ^ 2 - s * t + t ^ 2 = -1) (x y : V) :
    ω (blockWeyl hli hV s t x) (blockWeyl hli hV s t y) = ω x y := by
  have hskew : ∀ x y : V, ω y x = -ω x y := fun x y => (hω.neg_eq x y).symm
  have h1 : ω.compl₁₂ (blockWeyl hli hV s t) (blockWeyl hli hV s t) = ω := by
    refine LinearMap.BilinForm.ext_basis (blockBasis hli hV) fun i j => ?_
    rw [LinearMap.compl₁₂_apply, coe_blockBasis]
    have huu := hω u
    have hAuAu := hω (A u)
    have hww := hω w
    have hBwBw := hω (B w)
    have hAuu : ω (A u) u = -1 := by rw [hskew, huA]
    have hBww : ω (B w) w = -1 := by rw [hskew, hwB]
    have hwu : ω w u = 0 := by rw [hskew, huw, neg_zero]
    have hBwu : ω (B w) u = 0 := by rw [hskew, huBw, neg_zero]
    have hwAu : ω w (A u) = 0 := by rw [hskew, hAuw, neg_zero]
    have hBwAu : ω (B w) (A u) = 0 := by rw [hskew, hAuBw, neg_zero]
    fin_cases i <;> fin_cases j <;>
      simp [blockWeyl_u, blockWeyl_Au, blockWeyl_w, blockWeyl_Bw, huu, hAuAu, hww, hBwBw, hAuu,
        hBww, hwu, hBwu, hwAu, hBwAu, huA, hwB, huw, huBw, hAuw, hAuBw] <;>
      first | ring1 | linear_combination hst | linear_combination (-1 : K) * hst
  have := congrArg (fun F : LinearMap.BilinForm K V => F x y) h1
  simpa [LinearMap.compl₁₂_apply] using this

end Isometry

end Item424Res5

end CFSG.RankThree.PartTwo.Sec4
