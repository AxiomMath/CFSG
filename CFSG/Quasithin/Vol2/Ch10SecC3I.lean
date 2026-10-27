module

public import CFSG.Quasithin.Vol2.Ch10SecC3G
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut)
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def addMap (ψ : MulAut (WM K)) :
    Matrix (Fin 2) (Fin 2) K →+ Matrix (Fin 2) (Fin 2) K :=
  AddMonoidHom.toMultiplicative.symm ψ.toMonoidHom

theorem addMap_apply (ψ : MulAut (WM K)) (X : Matrix (Fin 2) (Fin 2) K) :
    addMap ψ X = Multiplicative.toAdd (ψ (Multiplicative.ofAdd X)) := rfl

@[expose] def u : SL K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def w [CharP K 2] : SL K :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two_of, CharTwo.neg_eq]⟩

@[expose] def d (t : Kˣ) : SL K := ⟨!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)], by
  simp [Matrix.det_fin_two_of]⟩

@[expose] def sel [CharP K 2] : Fin 2 → SL K
  | 0 => 1
  | 1 => w

theorem slFieldAut_u (σ : K ≃+* K) : slFieldAut K σ u = u := by
  ext i j
  change σ (((u : SL K) : Matrix (Fin 2) (Fin 2) K) i j) =
    ((u : SL K) : Matrix (Fin 2) (Fin 2) K) i j
  fin_cases i <;> fin_cases j <;> simp [u]

theorem slFieldAut_w [CharP K 2] (σ : K ≃+* K) : slFieldAut K σ w = w := by
  ext i j
  change σ (((w : SL K) : Matrix (Fin 2) (Fin 2) K) i j) =
    ((w : SL K) : Matrix (Fin 2) (Fin 2) K) i j
  fin_cases i <;> fin_cases j <;> simp [w]

theorem slFieldAut_sel [CharP K 2] (σ : K ≃+* K) (i : Fin 2) : slFieldAut K σ (sel i) = sel i := by
  fin_cases i
  · exact map_one _
  · exact slFieldAut_w σ

theorem slFieldAut_d (σ : K ≃+* K) (t : Kˣ) :
    slFieldAut K σ (d t) = d (Units.map σ.toRingHom.toMonoidHom t) := by
  ext i j
  change σ (((d t : SL K) : Matrix (Fin 2) (Fin 2) K) i j) = _
  fin_cases i <;> fin_cases j <;> simp [d]

theorem eq_single_of_fix {Y : Matrix (Fin 2) (Fin 2) K}
    (h1 : ((u : SL K) : Matrix (Fin 2) (Fin 2) K) * Y = Y)
    (h2 : Y * ((u : SL K) : Matrix (Fin 2) (Fin 2) K)ᵀ = Y) : Y = Matrix.single 0 0 (Y 0 0) := by
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h1 0) 1
  have e3 := congrFun (congrFun h2 0) 0
  have e4 := congrFun (congrFun h2 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at e1 e2 e3 e4
  simp [u] at e1 e2 e3 e4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1, e2, e3]

theorem rho_u_one_single (c : K) :
    rho K (u, 1) (Multiplicative.ofAdd (Matrix.single 0 0 c)) =
      Multiplicative.ofAdd (Matrix.single 0 0 c) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply] <;> simp [u]

theorem rho_one_u_single (c : K) :
    rho K (1, u) (Multiplicative.ofAdd (Matrix.single 0 0 c)) =
      Multiplicative.ofAdd (Matrix.single 0 0 c) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply] <;> simp [u]

theorem rho_d_one_single (t : Kˣ) (c : K) :
    rho K (d t, 1) (Multiplicative.ofAdd (Matrix.single 0 0 c)) =
      Multiplicative.ofAdd (Matrix.single 0 0 ((t : K) * c)) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply] <;> simp [d]

theorem rho_one_d_single (t : Kˣ) (c : K) :
    rho K (1, d t) (Multiplicative.ofAdd (Matrix.single 0 0 c)) =
      Multiplicative.ofAdd (Matrix.single 0 0 ((t : K) * c)) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply] <;> simp [d, mul_comm]

theorem rho_sel_single [CharP K 2] (i j : Fin 2) (c : K) :
    rho K (sel i, sel j) (Multiplicative.ofAdd (Matrix.single 0 0 c)) =
      Multiplicative.ofAdd (Matrix.single i j c) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho]
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> simp only [Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.transpose_apply] <;> simp [sel, w]

end CFSG.Quasithin.Vol2.Ch10.C3.Om
