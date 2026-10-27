module

public import CFSG.LocalAnalysis.StandardType.GGResIDefs
public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.StandardType.GGResIITransport
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCell
public import CFSG.LocalAnalysis.StandardType.GGResQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCount
public import CFSG.LinearAlgebra.OrthogonalFourMinusThreeMaximal
public import CFSG.LocalAnalysis.StandardType.GGResQTwoSideTypes
public import CFSG.GH74.Generic.S1.Exo.LinMinus
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import Mathlib.Tactic.FinCases
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.Defs
public import CFSG.Sporadic.McL

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev GGQTwoMat := Matrix (Fin 4) (Fin 4) (ZMod 3)

def S1 : GGQTwoMat := !![2,2,2,2; 2,2,0,0; 2,0,2,2; 2,0,2,1]
def S2 : GGQTwoMat := !![2,2,2,0; 2,2,0,2; 2,0,2,2; 0,2,2,1]
def S3 : GGQTwoMat := !![2,2,2,2; 2,2,0,0; 2,0,1,0; 2,0,0,1]
def S4 : GGQTwoMat := !![2,2,2,0; 2,2,0,2; 2,0,1,1; 0,2,1,1]
def S5 : GGQTwoMat := !![2,2,2,0; 2,1,0,1; 2,0,2,2; 0,1,2,1]

namespace GGQTwo

@[expose] def ggQTwoJ0 (ib : Fin 3) : Fin 3 := if ib = 0 then 1 else 0
@[expose] def ggQTwoJ1 (ib : Fin 3) : Fin 3 := if ib = 2 then 1 else 2

@[expose] def ggQTwoShapeC (D : GGResQTwoResidualData) : GGQTwoMat :=
  let j0 := ggQTwoJ0 D.ib
  let j1 := ggQTwoJ1 D.ib
  !![ (D.C j0 j0 : ZMod 3), (D.C j0 j1 : ZMod 3), (D.C j0 D.ib : ZMod 3),
        (if j0 = D.ic then (D.e₂ : ZMod 3) else 0);
      (D.C j1 j0 : ZMod 3), (D.C j1 j1 : ZMod 3), (D.C j1 D.ib : ZMod 3),
        (if j1 = D.ic then (D.e₂ : ZMod 3) else 0);
      (D.C D.ib j0 : ZMod 3), (D.C D.ib j1 : ZMod 3), 2, D.v;
      (if j0 = D.ic then (D.e₁ : ZMod 3) else 0),
        (if j1 = D.ic then (D.e₁ : ZMod 3) else 0), D.u, 2]

def ggQTwoS : Fin 5 → GGQTwoMat :=
  Fin.cases S1 <| Fin.cases S2 <| Fin.cases S3 <| Fin.cases S4 <| fun _ => S5

structure GGQTwoRec where
  C : GGQTwoMat
  d : Fin 4 → ZMod 3
  k : Fin 5
  p : Fin 4 → Fin 4
  s : Fin 4 → ZMod 3
  tag : GGResQTwoResidual
  hp : Function.Bijective p
  hC : ∀ i j, C i j = d i * s i * s j * ggQTwoS k (p i) (p j)
  hCdiag : ∀ i, C i i = 2
  hSsym : ∀ i j, d i * C i j = d j * C j i
  hdet : Matrix.det (fun i j => d i * C i j) = 2
  hd2 : ∀ i, d i * d i = 1
  hC_shape : C = ggQTwoShapeC (ggResQTwoResidualData tag)

def ggQTwoRecords : List GGQTwoRec := [
  ⟨!![2, 2, 2, 1; 2, 2, 0, 0; 2, 0, 2, 1; 2, 0, 2, 2], ![1, 1, 1, 2], 0, ![0, 1, 2, 3], ![1, 1, 1, 2], .A3b0c1w12,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 2, 2; 2, 2, 0, 0; 2, 0, 2, 2; 1, 0, 1, 2], ![1, 1, 1, 2], 0, ![0, 1, 2, 3], ![1, 1, 1, 1], .A3b0c1w21,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 2, 0; 2, 2, 0, 1; 2, 0, 2, 1; 0, 2, 2, 2], ![1, 1, 1, 2], 1, ![0, 1, 2, 3], ![1, 1, 1, 2], .A3b0c2w12,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 2, 0; 2, 2, 0, 2; 2, 0, 2, 2; 0, 1, 1, 2], ![1, 1, 1, 2], 1, ![0, 1, 2, 3], ![1, 1, 1, 1], .A3b0c2w21,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 1; 2, 2, 2, 0; 0, 2, 2, 1; 2, 0, 2, 2], ![1, 1, 1, 2], 1, ![1, 0, 2, 3], ![1, 1, 1, 2], .A3b2c0w12,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 2; 2, 2, 2, 0; 0, 2, 2, 2; 1, 0, 1, 2], ![1, 1, 1, 2], 1, ![1, 0, 2, 3], ![1, 1, 1, 1], .A3b2c0w21,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 0; 2, 2, 2, 1; 0, 2, 2, 1; 0, 2, 2, 2], ![1, 1, 1, 2], 0, ![1, 0, 2, 3], ![1, 1, 1, 2], .A3b2c1w12,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 0; 2, 2, 2, 2; 0, 2, 2, 2; 0, 1, 1, 2], ![1, 1, 1, 2], 0, ![1, 0, 2, 3], ![1, 1, 1, 1], .A3b2c1w21,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 1, 2, 0; 2, 2, 0, 2; 2, 0, 2, 1; 0, 2, 2, 2], ![1, 2, 1, 2], 3, ![0, 2, 1, 3], ![1, 2, 1, 2], .B3b0c2,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 2; 2, 2, 1, 0; 0, 2, 2, 2; 2, 0, 1, 2], ![1, 1, 2, 1], 1, ![0, 1, 3, 2], ![1, 1, 2, 1], .B3b2c0,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 1; 2, 2, 1, 0; 0, 2, 2, 2; 2, 0, 2, 2], ![1, 1, 2, 2], 3, ![0, 1, 3, 2], ![1, 1, 2, 2], .B3b2c0w12,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 2; 2, 2, 1, 0; 0, 2, 2, 1; 1, 0, 1, 2], ![1, 1, 2, 2], 3, ![0, 1, 3, 2], ![1, 1, 2, 1], .B3b2c0w21,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 0; 2, 2, 1, 2; 0, 2, 2, 2; 0, 2, 1, 2], ![1, 1, 2, 1], 0, ![1, 0, 3, 2], ![1, 1, 2, 1], .B3b2c1,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 0; 2, 2, 1, 1; 0, 2, 2, 0; 0, 2, 0, 2], ![1, 1, 2, 2], 2, ![1, 0, 2, 3], ![1, 1, 2, 2], .B3b2c1w12,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 0; 2, 2, 1, 2; 0, 2, 2, 0; 0, 1, 0, 2], ![1, 1, 2, 2], 2, ![1, 0, 2, 3], ![1, 1, 2, 1], .B3b2c1w21,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 2, 0; 1, 2, 0, 2; 2, 0, 2, 2; 0, 2, 1, 2], ![1, 2, 1, 2], 3, ![0, 2, 1, 3], ![1, 1, 1, 1], .C3b0c2,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 2; 2, 2, 2, 0; 0, 1, 2, 1; 2, 0, 2, 2], ![1, 1, 2, 1], 1, ![0, 1, 3, 2], ![1, 1, 1, 1], .C3b2c0,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 1; 2, 2, 2, 0; 0, 1, 2, 1; 2, 0, 1, 2], ![1, 1, 2, 2], 3, ![0, 1, 3, 2], ![1, 1, 1, 2], .C3b2c0w12,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 2; 2, 2, 2, 0; 0, 1, 2, 2; 1, 0, 2, 2], ![1, 1, 2, 2], 3, ![0, 1, 3, 2], ![1, 1, 1, 1], .C3b2c0w21,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 0; 2, 2, 2, 2; 0, 1, 2, 1; 0, 2, 2, 2], ![1, 1, 2, 1], 0, ![1, 0, 3, 2], ![1, 1, 1, 1], .C3b2c1,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 0; 2, 2, 2, 1; 0, 1, 2, 0; 0, 2, 0, 2], ![1, 1, 2, 2], 2, ![1, 0, 2, 3], ![1, 1, 1, 2], .C3b2c1w12,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩,
  ⟨!![2, 2, 0, 0; 2, 2, 2, 2; 0, 1, 2, 0; 0, 1, 0, 2], ![1, 1, 2, 2], 2, ![1, 0, 2, 3], ![1, 1, 1, 1], .C3b2c1w21,
    by decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by intro i; fin_cases i <;> decide,
    by intro i j; fin_cases i <;> fin_cases j <;> decide,
    by decide +kernel,
    by intro i; fin_cases i <;> decide,
    by decide⟩
]
open CFSG.StandardType

variable (r : GGQTwoRec)

def S (r : GGQTwoRec) : GGQTwoMat := fun i j => r.d i * r.C i j

def refl (C : GGQTwoMat) (i : Fin 4) (x : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  x - (fun _ : Fin 4 => (∑ j, C i j * x j : ZMod 3)) •
    (Pi.single i (1 : ZMod 3) : Fin 4 → ZMod 3)

lemma toQuadForm_apply (G : GGQTwoMat) (v : Fin 4 → ZMod 3) :
    (Matrix.toQuadraticForm' G) v = v ⬝ᵥ G.mulVec v := by
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

lemma S_isSymm (r : GGQTwoRec) : (S r).IsSymm := by
  ext i j
  exact (r.hSsym i j).symm

lemma polar_toQuadForm (G : GGQTwoMat) (hG : G.IsSymm)
    (x y : Fin 4 → ZMod 3) :
    QuadraticMap.polar (Matrix.toQuadraticForm' G) x y = 2 * (x ⬝ᵥ G.mulVec y) := by
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.polar_toQuadraticMap,
    Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply',
    hG.dotProduct_mulVec_comm]
  ring

lemma dot_eq (r : GGQTwoRec) (i : Fin 4) (x : Fin 4 → ZMod 3) :
    (Pi.single i (1 : ZMod 3) : Fin 4 → ZMod 3) ⬝ᵥ (S r).mulVec x =
      r.d i * ∑ j, r.C i j * x j := by
  simp [S, dotProduct, Matrix.mulVec, Pi.single_apply, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

lemma refl_invariant (r : GGQTwoRec) (i : Fin 4) (x : Fin 4 → ZMod 3) :
    (Matrix.toQuadraticForm' (S r)) (refl r.C i x) = (Matrix.toQuadraticForm' (S r)) x := by
  let Q := Matrix.toQuadraticForm' (S r)
  let hvec : Fin 4 → ZMod 3 := Pi.single i (1 : ZMod 3)
  have hQii : Q hvec = 2 * r.d i := by
    rw [toQuadForm_apply]
    simp [S, hvec, dotProduct, Matrix.mulVec, Pi.single_apply, r.hCdiag i]
    ring
  have hdi : r.d i ≠ 0 := by
    intro h
    have := r.hd2 i
    rw [h, mul_zero] at this
    exact zero_ne_one this
  have hQnz : Q hvec ≠ 0 := by
    rw [hQii]
    exact mul_ne_zero (by decide) hdi
  let : Invertible (Q hvec) := invertibleOfNonzero hQnz
  have hrefl : refl r.C i x = (TauCeti.QuadraticMap.reflection Q hvec) x := by
    rw [refl, TauCeti.QuadraticMap.reflection_apply,
      polar_toQuadForm (S r) (S_isSymm r)]
    congr 1
    have hcoef : ⅟(Q hvec) * (2 * (hvec ⬝ᵥ (S r).mulVec x)) = ∑ j, r.C i j * x j := by
      rw [invOf_eq_inv, hQii, dot_eq r]
      rw [show (2 * r.d i)⁻¹ = 2 * r.d i by
        apply inv_eq_of_mul_eq_one_right
        rw [show (2 * r.d i) * (2 * r.d i) = 4 * (r.d i * r.d i) by ring]
        rw [r.hd2 i]; decide]
      rw [show (2 * (r.d i * ∑ j, r.C i j * x j)) = 2 * r.d i * ∑ j, r.C i j * x j by ring]
      rw [show (2 * r.d i) * (2 * r.d i * ∑ j, r.C i j * x j) =
        ((2 * r.d i) * (2 * r.d i)) * ∑ j, r.C i j * x j by ring]
      rw [show (2 * r.d i) * (2 * r.d i) = 1 by
        rw [show (2 * r.d i) * (2 * r.d i) = 4 * (r.d i * r.d i) by ring, r.hd2 i]; decide]
      rw [one_mul]
    rw [hcoef]
    rfl
  rw [hrefl]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    (TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q hvec) x

lemma S_symm_eq (r : GGQTwoRec) : Matrix.transpose (S r) = S r := S_isSymm r

lemma hdet_nonsquare (r : GGQTwoRec) : ¬ IsSquare (S r).det := by
  change ¬ IsSquare (Matrix.det (fun i j => r.d i * r.C i j))
  rw [r.hdet]
  decide

lemma nondeg (r : GGQTwoRec) :
    (QuadraticMap.polarBilin (Matrix.toQuadraticForm' (S r))).Nondegenerate := by
  have h := CFSG.GH74.Generic.S1.Exo.toQuadraticForm_minus_of_det_nonsquare
    (K := ZMod 3) (by decide) (S r) (S_symm_eq r) (hdet_nonsquare r)
  exact h.1

lemma not_plus (r : GGQTwoRec) :
    ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Matrix.toQuadraticForm' (S r)) := by
  have h := CFSG.GH74.Generic.S1.Exo.toQuadraticForm_minus_of_det_nonsquare
    (K := ZMod 3) (by decide) (S r) (S_symm_eq r) (hdet_nonsquare r)
  exact h.2

lemma nondegenerate_compl12_equiv {W W' : Type}
    [AddCommGroup W] [Module (ZMod 3) W]
    [AddCommGroup W'] [Module (ZMod 3) W']
    (B : LinearMap.BilinForm (ZMod 3) W) (e : W' ≃ₗ[ZMod 3] W)
    (hB : B.Nondegenerate) :
    (B.compl₁₂ e.toLinearMap e.toLinearMap).Nondegenerate := by
  constructor
  · intro x hx
    apply e.injective
    rw [map_zero]
    apply hB.1 (e x)
    intro y
    have := hx (e.symm y)
    simpa [LinearMap.compl₁₂_apply] using this
  · intro y hy
    apply e.injective
    rw [map_zero]
    apply hB.2 (e y)
    intro x
    have := hy (e.symm x)
    simpa [LinearMap.compl₁₂_apply] using this

@[simp] lemma ggResIIIdx_zero {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResIIIdx e (0 : Fin 4) = some (e 0) := by
  change ggResIIIdx e ((0 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 0

@[simp] lemma ggResIIIdx_one {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResIIIdx e (1 : Fin 4) = some (e 1) := by
  change ggResIIIdx e ((1 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 1

@[simp] lemma ggResIIIdx_two {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResIIIdx e (2 : Fin 4) = some (e 2) := by
  change ggResIIIdx e ((2 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 2

@[simp] lemma ggResIIIdx_three {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResIIIdx e (3 : Fin 4) = none := by
  change ggResIIIdx e (Fin.last 3) = _
  exact ggResIIIdx_last e

@[simp] lemma ggResQTwoCarrierPoint_0_0 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 0 0 = some (e 1) := by
  change ggResIIIdx e ((1 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 1

@[simp] lemma ggResQTwoCarrierPoint_0_1 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 0 1 = some (e 2) := by
  change ggResIIIdx e ((2 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 2

@[simp] lemma ggResQTwoCarrierPoint_0_2 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 0 2 = some (e 0) := by
  change ggResIIIdx e ((0 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 0

@[simp] lemma ggResQTwoCarrierPoint_0_3 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 0 3 = none := by
  change ggResIIIdx e (Fin.last 3) = _
  exact ggResIIIdx_last e

@[simp] lemma ggResQTwoCarrierPoint_1_0 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 1 0 = some (e 0) := by
  change ggResIIIdx e ((0 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 0

@[simp] lemma ggResQTwoCarrierPoint_1_1 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 1 1 = some (e 2) := by
  change ggResIIIdx e ((2 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 2

@[simp] lemma ggResQTwoCarrierPoint_1_2 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 1 2 = some (e 1) := by
  change ggResIIIdx e ((1 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 1

@[simp] lemma ggResQTwoCarrierPoint_1_3 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 1 3 = none := by
  change ggResIIIdx e (Fin.last 3) = _
  exact ggResIIIdx_last e

@[simp] lemma ggResQTwoCarrierPoint_2_0 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 2 0 = some (e 0) := by
  change ggResIIIdx e ((0 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 0

@[simp] lemma ggResQTwoCarrierPoint_2_1 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 2 1 = some (e 1) := by
  change ggResIIIdx e ((1 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 1

@[simp] lemma ggResQTwoCarrierPoint_2_2 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 2 2 = some (e 2) := by
  change ggResIIIdx e ((2 : Fin 3).castSucc) = _
  exact ggResIIIdx_castSucc e 2

@[simp] lemma ggResQTwoCarrierPoint_2_3 {Λ : Type} (e : Fin 3 ≃ Λ) :
    ggResQTwoCarrierPoint e 2 3 = none := by
  change ggResIIIdx e (Fin.last 3) = _
  exact ggResIIIdx_last e

theorem ggQTwoCarrierPairing
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {CL : Matrix Λ Λ ℤ} {b : Λ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {C : Matrix (Fin 3) (Fin 3) ℤ} {ib ic : Fin 3} {e₁ e₂ : ℤ}
    {u v : ZMod 3} {e : Fin 3 ≃ Λ} {tag : GGResQTwoResidual}
    {α : Option Λ → Module.Dual (ZMod 3) V} {h : Option Λ → V}
    (hib : e ib = b)
    (hres : GGResQTwoResidualShape tag 3 C ib ic e₁ e₂ u v)
    (hCe : ∀ i j, CL (e i) (e j) = C i j)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod 3))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod 3))
    (hrow : ∀ (j : Fin 3) (hj : e j ≠ b),
      CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0)
    (hcol : ∀ (j : Fin 3) (hj : e j ≠ b),
      CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0)
    (hdiagK : CK none none = 2)
    (huCross : u = α none (h (some b)))
    (hvCross : v = α (some b) (h none)) (i j : Fin 4) :
    α (ggResQTwoCarrierPoint e ib i) (h (ggResQTwoCarrierPoint e ib j)) =
      ggQTwoShapeC (ggResQTwoResidualData tag) i j := by
  have hsome : ∀ i j : Fin 3,
      α (some (e i)) (h (some (e j))) = (C i j : ZMod 3) := by
    intro i j
    rw [hL, hCe]
  have hrowAll : ∀ j : Fin 3, α none (h (some (e j))) =
      if j = ib then u else if j = ic then (e₁ : ZMod 3) else 0 := by
    intro j
    by_cases hj : j = ib
    · subst j
      simp [hib, huCross]
    · have hne : e j ≠ b := by
        intro he
        exact hj (e.injective (he.trans hib.symm))
      rw [if_neg hj]
      calc
        α none (h (some (e j))) = (CK none (some ⟨e j, hne⟩) : ZMod 3) := by
          simpa using hK none (some ⟨e j, hne⟩)
        _ = ((if j = ic then e₁ else 0 : ℤ) : ZMod 3) := by rw [hrow j hne]
        _ = if j = ic then (e₁ : ZMod 3) else 0 := by split_ifs <;> rfl
  have hcolAll : ∀ j : Fin 3, α (some (e j)) (h none) =
      if j = ib then v else if j = ic then (e₂ : ZMod 3) else 0 := by
    intro j
    by_cases hj : j = ib
    · subst j
      simp [hib, hvCross]
    · have hne : e j ≠ b := by
        intro he
        exact hj (e.injective (he.trans hib.symm))
      rw [if_neg hj]
      calc
        α (some (e j)) (h none) = (CK (some ⟨e j, hne⟩) none : ZMod 3) := by
          simpa using hK (some ⟨e j, hne⟩) none
        _ = ((if j = ic then e₂ else 0 : ℤ) : ZMod 3) := by rw [hcol j hne]
        _ = if j = ic then (e₂ : ZMod 3) else 0 := by split_ifs <;> rfl
  have hdiagA : α none (h none) = (2 : ZMod 3) := by
    simpa [hdiagK] using hK none none
  obtain ⟨hC, hibD, hicD, he1, he2, hu, hv⟩ := hres
  have hdiagC : ∀ k : Fin 3, C k k = 2 := by
    rw [hC]
    cases tag <;> intro k <;> fin_cases k <;> decide
  simp only [ggQTwoShapeC]
  rw [← hC, ← hibD, ← hicD, ← he1, ← he2, ← hu, ← hv]
  fin_cases ib <;> fin_cases i <;> fin_cases j <;>
    simp [ggQTwoJ0, ggQTwoJ1, hsome, hrowAll, hcolAll, hdiagA, hdiagC]

def fixed : GGResQTwoResidual → Fin 4 → ZMod 3
  | .A3b0c1w12 => ![1, 2, 1, 1]
  | .A3b0c1w21 => ![1, 2, 1, 2]
  | .A3b0c2w12 => ![1, 0, 2, 1]
  | .A3b0c2w21 => ![1, 0, 2, 2]
  | .A3b2c0w12 => ![0, 1, 2, 1]
  | .A3b2c0w21 => ![0, 1, 2, 2]
  | .A3b2c1w12 => ![1, 2, 2, 2]
  | .A3b2c1w21 => ![1, 2, 2, 1]
  | .B3b0c2 => ![1, 1, 0, 1]
  | .B3b2c0 => ![1, 0, 1, 2]
  | .B3b2c0w12 => ![0, 1, 1, 1]
  | .B3b2c0w21 => ![0, 1, 1, 2]
  | .B3b2c1 => ![1, 2, 2, 2]
  | .B3b2c1w12 => ![1, 2, 1, 2]
  | .B3b2c1w21 => ![1, 2, 1, 1]
  | .C3b0c2 => ![1, 2, 0, 2]
  | .C3b2c0 => ![1, 0, 2, 2]
  | .C3b2c0w12 => ![0, 1, 2, 1]
  | .C3b2c0w21 => ![0, 1, 2, 2]
  | .C3b2c1 => ![1, 2, 1, 2]
  | .C3b2c1w12 => ![1, 2, 2, 2]
  | .C3b2c1w21 => ![1, 2, 2, 1]

def selectedSide : GGResQTwoResidual → List (Fin 4)
  | .A3b0c1w12 => [0, 1, 3]
  | .A3b0c1w21 => [0, 1, 3]
  | .A3b0c2w12 => [0, 1, 3]
  | .A3b0c2w21 => [0, 1, 3]
  | .A3b2c0w12 => [0, 1, 3]
  | .A3b2c0w21 => [0, 1, 3]
  | .A3b2c1w12 => [0, 1, 3]
  | .A3b2c1w21 => [0, 1, 3]
  | .B3b0c2 => [0, 1, 2]
  | .B3b2c0 => [0, 1, 2]
  | .B3b2c0w12 => [0, 1, 2]
  | .B3b2c0w21 => [0, 1, 2]
  | .B3b2c1 => [0, 1, 2]
  | .B3b2c1w12 => [0, 1, 2]
  | .B3b2c1w21 => [0, 1, 2]
  | .C3b0c2 => [0, 1, 2]
  | .C3b2c0 => [0, 1, 2]
  | .C3b2c0w12 => [0, 1, 2]
  | .C3b2c0w21 => [0, 1, 2]
  | .C3b2c1 => [0, 1, 2]
  | .C3b2c1w12 => [0, 1, 2]
  | .C3b2c1w21 => [0, 1, 2]

def extra : GGResQTwoResidual → Fin 4
  | .A3b0c1w12 => 2
  | .A3b0c1w21 => 2
  | .A3b0c2w12 => 2
  | .A3b0c2w21 => 2
  | .A3b2c0w12 => 2
  | .A3b2c0w21 => 2
  | .A3b2c1w12 => 2
  | .A3b2c1w21 => 2
  | .B3b0c2 => 3
  | .B3b2c0 => 3
  | .B3b2c0w12 => 3
  | .B3b2c0w21 => 3
  | .B3b2c1 => 3
  | .B3b2c1w12 => 3
  | .B3b2c1w21 => 3
  | .C3b0c2 => 3
  | .C3b2c0 => 3
  | .C3b2c0w12 => 3
  | .C3b2c0w21 => 3
  | .C3b2c1 => 3
  | .C3b2c1w12 => 3
  | .C3b2c1w21 => 3

def fixedNormOK (r : GGQTwoRec) : Bool :=
  decide ((Matrix.toQuadraticForm' (S r)) (fixed r.tag) = 2)

theorem fixedNormOK_all : ggQTwoRecords.all fixedNormOK = true := by
  decide +kernel

theorem fixed_norm (r : GGQTwoRec) (hr : r ∈ ggQTwoRecords) :
    (Matrix.toQuadraticForm' (S r)) (fixed r.tag) = 2 := by
  have h := List.all_eq_true.mp fixedNormOK_all r hr
  exact of_decide_eq_true h

def fixedSideOK (r : GGQTwoRec) : Bool :=
  (selectedSide r.tag).all fun i => decide (refl r.C i (fixed r.tag) = fixed r.tag)

theorem fixedSideOK_all : ggQTwoRecords.all fixedSideOK = true := by
  decide +kernel

theorem fixed_side (r : GGQTwoRec) (hr : r ∈ ggQTwoRecords) (i : Fin 4)
    (hi : i ∈ selectedSide r.tag) :
    refl r.C i (fixed r.tag) = fixed r.tag := by
  have h := List.all_eq_true.mp fixedSideOK_all r hr
  have h' := List.all_eq_true.mp h i hi
  exact of_decide_eq_true h'

def fixedExtraOK (r : GGQTwoRec) : Bool :=
  ([0, 1, 2] : List (ZMod 3)).all fun c =>
    ([0, 1, 2, 3] : List (Fin 4)).any fun j =>
      decide (refl r.C (extra r.tag) (fixed r.tag) j ≠ (c • fixed r.tag) j)

theorem fixedExtraOK_all : ggQTwoRecords.all fixedExtraOK = true := by
  decide +kernel

theorem fixed_extra_ne_smul (r : GGQTwoRec) (hr : r ∈ ggQTwoRecords) (c : ZMod 3) :
    refl r.C (extra r.tag) (fixed r.tag) ≠ c • fixed r.tag := by
  intro h
  have hc_mem : c ∈ ([0, 1, 2] : List (ZMod 3)) := by
    rcases ggResQTwoZMod3_cases c with rfl | rfl | rfl <;> simp
  have h1 : fixedExtraOK r = true := List.all_eq_true.mp fixedExtraOK_all r hr
  have h2 : (([0, 1, 2] : List (ZMod 3)).all fun c =>
      ([0, 1, 2, 3] : List (Fin 4)).any fun j =>
        decide (refl r.C (extra r.tag) (fixed r.tag) j ≠ (c • fixed r.tag) j)) = true := by
    simpa only [fixedExtraOK] using h1
  have h3 : (([0, 1, 2, 3] : List (Fin 4)).any fun j =>
      decide (refl r.C (extra r.tag) (fixed r.tag) j ≠ (c • fixed r.tag) j)) = true :=
    List.all_eq_true.mp h2 c hc_mem
  obtain ⟨j, _, hj⟩ := List.any_eq_true.mp h3
  exact of_decide_eq_true hj (congrFun h j)

theorem fixed_extra_not_span (r : GGQTwoRec) (hr : r ∈ ggQTwoRecords) :
    refl r.C (extra r.tag) (fixed r.tag) ∉
      Submodule.span (ZMod 3) ({fixed r.tag} : Set (Fin 4 → ZMod 3)) := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact fixed_extra_ne_smul r hr c (by rw [hc])

theorem orthogonalGroup_eq_top_of_side
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4)
    (hminus : ¬ ∃ U : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) U = 2 ∧ ∀ u ∈ U, Q u = 0)
    {H S : Subgroup (V ≃ₗ[ZMod 3] V)} {w : V}
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hSH : S ≤ H)
    (hScard : Nat.card ↥S = 48)
    (hw : Q w ≠ 0) (hSfix : ∀ s ∈ S, s w = w)
    (hmove : ∃ g ∈ H, g w ∉ Submodule.span (ZMod 3) {w}) :
    H = TauCeti.QuadraticMap.orthogonalGroup Q := by
  have hSO : S ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hSH.trans hHO
  have hstab : OrthF3.fullVectorStabilizer Q w ≤ S :=
    OrthF3.fullVectorStabilizer_le_of_le_orthogonalGroup_of_card_eq Q hQ hd w hw hSO hSfix hScard
  refine CFSG.LinearAlgebra.OrthogonalFourMinusThree.orthogonalGroup_eq_top_of_stabilizer_le
    Q hQ hd hminus hw hHO ?_ hmove
  intro a ha hafix
  apply hSH
  apply hstab
  rw [OrthF3.mem_fullVectorStabilizer_iff]
  exact ⟨hafix, ha⟩

theorem actualJoin_card_eq_1440
    {G : Type} [Group G] {Bs L K : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4)
    (hminus : ¬ ∃ U : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) U = 2 ∧ ∀ u ∈ U, Q u = 0)
    (hinv : ∀ a ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ v,
      Q (ggLin (p := 3) ι a v) = Q v)
    (S : Subgroup (MulAut ↥Bs))
    (hSA : S ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hScard : Nat.card ↥S = 48)
    (w : V) (hw : Q w ≠ 0)
    (hSfix : ∀ s ∈ S, ggLin (p := 3) ι s w = w)
    (hextra : ∃ e ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs,
      ggLin (p := 3) ι e w ∉ Submodule.span (ZMod 3) {w}) :
    Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 1440 := by
  have : FiniteDimensional (ZMod 3) V := FiniteDimensional.of_finrank_pos (by omega)
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let H : Subgroup (V ≃ₗ[ZMod 3] V) := A.map (ggLin (p := 3) ι)
  let S' : Subgroup (V ≃ₗ[ZMod 3] V) := S.map (ggLin (p := 3) ι)
  have hinj : Function.Injective (ggLin (p := 3) ι) := ggLin_injective ι
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨a, ha, rfl⟩
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    exact hinv a ha
  have hSH : S' ≤ H := Subgroup.map_mono hSA
  have hS'card : Nat.card S' = 48 := by
    rw [Subgroup.card_map_of_injective (f := ggLin (p := 3) ι) hinj, hScard]
  have hS'fix : ∀ s ∈ S', s w = w := by
    rintro _ ⟨s, hs, rfl⟩
    exact hSfix s hs
  have hmove : ∃ g ∈ H, g w ∉ Submodule.span (ZMod 3) {w} := by
    obtain ⟨e, he, hm⟩ := hextra
    exact ⟨ggLin (p := 3) ι e, Subgroup.mem_map_of_mem (f := ggLin (p := 3) ι) he, hm⟩
  have hHtop : H = TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthogonalGroup_eq_top_of_side Q hQ hd hminus hHO hSH hS'card hw hS'fix hmove
  have hcardH : Nat.card ↥H = 1440 := by
    rw [hHtop]
    exact OrthF3.card_orthogonalGroup_four_minus Q hQ hd hminus
  have hcardHA : Nat.card ↥H = Nat.card ↥A :=
    Subgroup.card_map_of_injective (f := ggLin (p := 3) ι) hinj
  exact hcardHA.symm.trans hcardH

theorem actualJoin_ggIsGOFourMinusThree
    {G : Type} [Group G] {Bs L K : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (Q : QuadraticForm (ZMod 3) V)
    (hcardBs : Nat.card ↥Bs = 3 ^ 4)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4)
    (hminus : ¬ ∃ U : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) U = 2 ∧ ∀ u ∈ U, Q u = 0)
    (hinv : ∀ a ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ v,
      Q (ggLin (p := 3) ι a v) = Q v)
    (S : Subgroup (MulAut ↥Bs))
    (hSA : S ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hScard : Nat.card ↥S = 48)
    (w : V) (hw : Q w ≠ 0)
    (hSfix : ∀ s ∈ S, ggLin (p := 3) ι s w = w)
    (hextra : ∃ e ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs,
      ggLin (p := 3) ι e w ∉ Submodule.span (ZMod 3) {w}) :
    GGIsGOFourMinusThree (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  refine ⟨hcardBs, actualJoin_card_eq_1440 ι Q hQ hd hminus hinv S hSA hScard w hw hSfix hextra,
    V, inferInstance, inferInstance, ι, Q, hQ, hinv⟩

section Transport

variable {G : Type} [Group G] {Bs : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  (ι : Additive ↥Bs ≃+ V) (coord : V ≃ₗ[ZMod 3] (Fin 4 → ZMod 3))
  (r : GGQTwoRec)

theorem fixes_transported (hr : r ∈ ggQTwoRecords) (s : MulAut ↥Bs) (i : Fin 4)
    (hcoord : ∀ v : V, coord (ggLin (p := 3) ι s v) = refl r.C i (coord v))
    (hi : i ∈ selectedSide r.tag) :
    ggLin (p := 3) ι s (coord.symm (fixed r.tag)) = coord.symm (fixed r.tag) := by
  apply coord.injective
  rw [hcoord, LinearEquiv.apply_symm_apply, fixed_side r hr i hi]

theorem moves_transported (hr : r ∈ ggQTwoRecords) (e : MulAut ↥Bs)
    (hcoord : ∀ v : V, coord (ggLin (p := 3) ι e v) = refl r.C (extra r.tag) (coord v)) :
    ggLin (p := 3) ι e (coord.symm (fixed r.tag)) ∉
      Submodule.span (ZMod 3) ({coord.symm (fixed r.tag)} : Set V) := by
  intro hmem
  have hmap : Submodule.map coord.toLinearMap
      (Submodule.span (ZMod 3) ({coord.symm (fixed r.tag)} : Set V)) =
      Submodule.span (ZMod 3) ({fixed r.tag} : Set (Fin 4 → ZMod 3)) := by
    rw [Submodule.map_span, Set.image_singleton]
    simp
  have hmem' : coord (ggLin (p := 3) ι e (coord.symm (fixed r.tag))) ∈
      Submodule.map coord.toLinearMap
        (Submodule.span (ZMod 3) ({coord.symm (fixed r.tag)} : Set V)) :=
    Submodule.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [hmap, hcoord, LinearEquiv.apply_symm_apply] at hmem'
  exact fixed_extra_not_span r hr hmem'

end Transport

theorem actualJoin_ggIsGOFourMinusThree_of_generators
    {G : Type} [Group G] {Bs L K : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (Q : QuadraticForm (ZMod 3) V)
    (coord : V ≃ₗ[ZMod 3] (Fin 4 → ZMod 3))
    (r : GGQTwoRec) (hr : r ∈ ggQTwoRecords)
    (hcardBs : Nat.card ↥Bs = 3 ^ 4)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4)
    (hminus : ¬ ∃ U : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) U = 2 ∧ ∀ u ∈ U, Q u = 0)
    (hQcoord : ∀ v : V, Q v = (Matrix.toQuadraticForm' (S r)) (coord v))
    (hinv : ∀ a ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ v,
      Q (ggLin (p := 3) ι a v) = Q v)
    (gen : (i : Fin 4) → i ∈ selectedSide r.tag → MulAut ↥Bs)
    (hSA : Subgroup.closure
      (Set.range (fun i : {i : Fin 4 // i ∈ selectedSide r.tag} => gen i.1 i.2)) ≤
      ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hScard : Nat.card ↥(Subgroup.closure
      (Set.range (fun i : {i : Fin 4 // i ∈ selectedSide r.tag} => gen i.1 i.2))) = 48)
    (hgencoord : ∀ (i : {i : Fin 4 // i ∈ selectedSide r.tag}) (v : V),
      coord (ggLin (p := 3) ι (gen i.1 i.2) v) = refl r.C i.1 (coord v))
    (hextra_coord : ∃ e ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs,
      ∀ v : V, coord (ggLin (p := 3) ι e v) =
        refl r.C (extra r.tag) (coord v)) :
    GGIsGOFourMinusThree (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  let S : Subgroup (MulAut ↥Bs) := Subgroup.closure
    (Set.range (fun i : {i : Fin 4 // i ∈ selectedSide r.tag} => gen i.1 i.2))
  set w : V := coord.symm (fixed r.tag)
  have hw : Q w ≠ 0 := by
    rw [hQcoord, LinearEquiv.apply_symm_apply, fixed_norm r hr]
    decide
  have hgenfix : ∀ i : {i : Fin 4 // i ∈ selectedSide r.tag},
      ggLin (p := 3) ι (gen i.1 i.2) w = w := by
    intro i
    exact fixes_transported ι coord r hr (gen i.1 i.2) i.1 (hgencoord i) i.2
  have hSfix : ∀ s ∈ S, ggLin (p := 3) ι s w = w := by
    intro s hs
    dsimp only [S] at hs
    induction hs using Subgroup.closure_induction with
    | mem g hg =>
        obtain ⟨i, rfl⟩ := hg
        exact hgenfix i
    | one => simp
    | mul x y _ _ hx hy =>
        rw [map_mul, LinearEquiv.mul_apply, hy, hx]
    | inv x _ hx =>
        rw [map_inv]
        apply (ggLin (p := 3) ι x).injective
        change (ggLin (p := 3) ι x) ((ggLin (p := 3) ι x).symm w) =
          (ggLin (p := 3) ι x) w
        rw [LinearEquiv.apply_symm_apply, hx]
  have hSA' : S ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    simpa only [S] using hSA
  have hScard' : Nat.card ↥S = 48 := by
    simpa only [S] using hScard
  obtain ⟨e, he, hcoord⟩ := hextra_coord
  have hextra : ∃ e ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs,
      ggLin (p := 3) ι e w ∉ Submodule.span (ZMod 3) ({w} : Set V) :=
    ⟨e, he, moves_transported ι coord r hr e hcoord⟩
  exact actualJoin_ggIsGOFourMinusThree ι Q hcardBs hQ hd hminus hinv S hSA' hScard'
    w hw hSfix hextra

end GGQTwo

namespace GGQTwo

theorem selectedSide_eq (tag : GGResQTwoResidual) :
    selectedSide tag = if ggResQTwoIsA3 tag then [0,1,3] else [0,1,2] := by
  cases tag <;> rfl

theorem LOrder_eq (tag : GGResQTwoResidual) :
    ggResQTwoLOrder tag = if ggResQTwoIsA3 tag then 24 else 48 := by
  cases tag <;> rfl

private theorem carrier_last {Λ : Type} (e : Fin 3 ≃ Λ) (ib : Fin 3) :
    ggResQTwoCarrierPoint e ib 3 = none := by
  fin_cases ib <;> simp

private theorem carrier_deleted {Λ : Type} (e : Fin 3 ≃ Λ) (ib : Fin 3) :
    ggResQTwoCarrierPoint e ib 2 = some (e ib) := by
  fin_cases ib <;> simp

theorem carrier_L_range {Λ X : Type} (e : Fin 3 ≃ Λ) (ib : Fin 3) (φ : Option Λ → X) :
    Set.range (fun i : {i : Fin 4 // i ∈ ([0,1,2] : List (Fin 4))} =>
      φ (ggResQTwoCarrierPoint e ib i.1)) = Set.range (fun j : Λ => φ (some j)) := by
  let π := ggResQTwoCarrierPoint e ib
  have hπ3 : π 3 = none := carrier_last e ib
  have hinj : Function.Injective π := ggResQTwoCarrierPoint_injective e ib
  have hsurj : Function.Surjective π :=
    (ggResIIIdx_surjective e).comp
      (Finite.injective_iff_surjective.mp (ggResQTwoCarrierIdx_injective ib))
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    have hi3 : i.1 ≠ 3 := by intro h; simpa [h] using i.2
    cases hpi : π i.1 with
    | none => exact (hi3 (hinj (hpi.trans hπ3.symm))).elim
    | some j => exact ⟨j, congrArg φ hpi.symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := hsurj (some j)
    have hi3 : i ≠ 3 := by intro h; rw [h,hπ3] at hi; cases hi
    have hm : i ∈ ([0,1,2] : List (Fin 4)) := by fin_cases i <;> simp_all
    exact ⟨⟨i,hm⟩,congrArg φ hi⟩

theorem carrier_K_range {Λ X : Type} {b : Λ} (e : Fin 3 ≃ Λ) (ib : Fin 3)
    (hib : e ib = b) (φ : Option Λ → X) :
    Set.range (fun i : {i : Fin 4 // i ∈ ([0,1,3] : List (Fin 4))} =>
      φ (ggResQTwoCarrierPoint e ib i.1)) =
      Set.range (fun j : {j : Λ // j ≠ b} => φ (some j.1)) ∪ {φ none} := by
  let π := ggResQTwoCarrierPoint e ib
  have hπ2 : π 2 = some b := by
    change ggResQTwoCarrierPoint e ib 2 = some b
    rw [carrier_deleted e ib,hib]
  have hinj : Function.Injective π := ggResQTwoCarrierPoint_injective e ib
  have hsurj : Function.Surjective π :=
    (ggResIIIdx_surjective e).comp
      (Finite.injective_iff_surjective.mp (ggResQTwoCarrierIdx_injective ib))
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    have hi2 : i.1 ≠ 2 := by intro h; simpa [h] using i.2
    cases hpi : π i.1 with
    | none => exact Or.inr (congrArg φ hpi)
    | some j =>
      have hj : j ≠ b := by intro h; rw [h] at hpi; exact hi2 (hinj (hpi.trans hπ2.symm))
      exact Or.inl ⟨⟨j,hj⟩,congrArg φ hpi.symm⟩
  · rintro (⟨j, rfl⟩ | rfl)
    · obtain ⟨i,hi⟩ := hsurj (some j.1)
      have hi2 : i ≠ 2 := by
        intro h
        rw [h,hπ2] at hi
        exact j.2 (Option.some.inj hi.symm)
      have hm : i ∈ ([0,1,3] : List (Fin 4)) := by fin_cases i <;> simp_all
      exact ⟨⟨i,hm⟩,congrArg φ hi⟩
    · refine ⟨⟨3,by simp⟩,?_⟩
      exact congrArg φ (carrier_last e ib)

end GGQTwo

theorem ggResQTwoGOForm
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFix : GGTBFixInput)
    (hLD : GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8)
      GGResQTwoResidualCell) :
    GGIsGOFourMinusThree (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWeylL, hCartL, hWeylK, hCartK, htyp, hrefl, hIsRefl, hCL, hCK, hsel,
    hfL, hfK, hAL, hAK, hconn, hAJ, hcell⟩ := hLD
  obtain ⟨n, C, ib, ic, e₁, e₂, e, tag, hCe, hib, hrow, hcol, hdiagK, hshape⟩ := hcell
  have hn : n = 3 := ggResQTwoResidualShape_n_eq_three tag n C ib ic e₁ e₂ _ _ hshape
  subst n
  have hrExists : ∀ tag : GGResQTwoResidual,
      ∃ r ∈ GGQTwo.ggQTwoRecords, r.tag = tag := by
    intro tag
    cases tag <;> simp [GGQTwo.ggQTwoRecords]
  obtain ⟨r, hr, hrtag⟩ := hrExists tag
  let π : Fin 4 → Option Λ := ggResQTwoCarrierPoint e ib
  have hπsurj : Function.Surjective π :=
    (ggResIIIdx_surjective e).comp
      (Finite.injective_iff_surjective.mp (ggResQTwoCarrierIdx_injective ib))
  have hCα : ∀ i j : Fin 4, α (π i) (h (π j)) = r.C i j := by
    intro i j
    rw [r.hC_shape, hrtag]
    exact GGQTwo.ggQTwoCarrierPairing hib hshape hCe hCL hCK hrow hcol hdiagK rfl rfl i j
  have hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤ :=
    ggResI_span_top hFix hH ι hrefl hAL hsel
  have hcardΛ : Fintype.card Λ = 3 := by
    simpa using (Fintype.card_congr e).symm
  have hdim : Module.finrank (ZMod 3) V = 4 := by
    rw [ggResI_finrank hspan hsel, hcardΛ]
  let bV : Module.Basis (Fin 4) (ZMod 3) V :=
    ggResQTwoCarrierBasis (e := e) ib h hsel hspan
  have hbV : ∀ i, bV i = h (π i) :=
    ggResQTwoCarrierBasis_apply (e := e) ib h hsel hspan
  let coord : V ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) := bV.equivFun
  have coord_h : ∀ i : Fin 4, coord (h (π i)) = Pi.single i (1 : ZMod 3) := by
    intro i
    rw [← hbV i]
    funext j
    rw [Module.Basis.equivFun_self]
    by_cases hji : i = j
    · subst hji; simp
    · simp [hji]
  have alpha_coord : ∀ (i : Fin 4) (w : V),
      α (π i) w = ∑ j, r.C i j * coord w j := by
    intro i w
    conv_lhs => rw [← bV.sum_equivFun w]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    calc ∑ j, coord w j * α (π i) (bV j)
        = ∑ j, coord w j * r.C i j := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [show bV j = h (π j) from hbV j, hCα i j]
      _ = ∑ j, r.C i j * coord w j := by
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
  let q : QuadraticForm (ZMod 3) (Fin 4 → ZMod 3) := Matrix.toQuadraticForm' (GGQTwo.S r)
  let Q : QuadraticForm (ZMod 3) V := q.comp coord.toLinearMap
  have hgen_i : ∀ (i : Fin 4) (w : V),
      Q (ggLin (p := 3) ι (φ (π i)) w) = Q w := by
    intro i w
    rw [hrefl (π i) w]
    change q (coord (w - α (π i) w • h (π i))) = q (coord w)
    rw [map_sub, map_smul, coord_h i, alpha_coord i w]
    exact GGQTwo.refl_invariant r i (coord w)
  have hgen_o : ∀ (o : Option Λ) (w : V), Q (ggLin (p := 3) ι (φ o) w) = Q w := by
    intro o w
    obtain ⟨i, rfl⟩ := hπsurj o
    exact hgen_i i w
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    change (QuadraticMap.polarBilin (q.comp coord.toLinearMap)).Nondegenerate
    rw [QuadraticMap.polarBilin_comp]
    exact GGQTwo.nondegenerate_compl12_equiv (QuadraticMap.polarBilin q) coord (GGQTwo.nondeg r)
  have hQnp : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
    intro hplus
    apply GGQTwo.not_plus r
    obtain ⟨U, hU, hUzero⟩ := hplus
    refine ⟨U.map coord.toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hU, hdim]
      simp
    · rintro _ ⟨u, hu, rfl⟩
      exact hUzero u hu
  have hcardBs : Nat.card Bs = 3 ^ 4 := by
    have : Finite V := Finite.of_equiv _ ι.toEquiv
    rw [card_eq_of_ggLin ι, ← FiniteField.pow_finrank_eq_natCard 3 V, hdim]
  have hAeq : ggAutomizer L Bs ⊔ ggAutomizer K Bs =
      Subgroup.closure (Set.range φ) := ggResI_sup_eq_closure hAL hAK
  have hgenH : ∀ o : Option Λ,
      ggLin (p := 3) ι (φ o) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro o
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    exact hgen_o o
  have hAle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap (ggLin (p := 3) ι) := by
    rw [hAeq]
    exact (Subgroup.closure_le _).mpr (by rintro _ ⟨o, rfl⟩; exact hgenH o)
  have hinv : ∀ a ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ v,
      Q (ggLin (p := 3) ι a v) = Q v := by
    intro a ha v
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hAle ha)) v
  obtain ⟨fL, hfL⟩ := hfL
  obtain ⟨fK, hfK⟩ := hfK
  let gen (i : Fin 4) (_ : i ∈ GGQTwo.selectedSide r.tag) : MulAut ↥Bs := φ (π i)
  have hSA : Subgroup.closure
      (Set.range (fun i : {i : Fin 4 // i ∈ GGQTwo.selectedSide r.tag} => gen i.1 i.2)) ≤
      ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    rw [hAeq]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨π i.1, rfl⟩
  have hScard : Nat.card ↥(Subgroup.closure
      (Set.range (fun i : {i : Fin 4 // i ∈ GGQTwo.selectedSide r.tag} => gen i.1 i.2))) = 48 := by
    dsimp only [gen]
    by_cases hA : ggResQTwoIsA3 tag = true
    · have hs : GGQTwo.selectedSide r.tag = [0,1,3] := by
        rw [hrtag, GGQTwo.selectedSide_eq, hA]
        rfl
      rw [hs, GGQTwo.carrier_K_range e ib hib φ, ← hAK]
      exact ggResQTwoResidual_A3_K_order hA hshape hWeylK hCartK hib hrow hcol fK
    · have hs : GGQTwo.selectedSide r.tag = [0,1,2] := by
        rw [hrtag, GGQTwo.selectedSide_eq]
        simp only [Bool.not_eq_true] at hA
        rw [hA]
        rfl
      rw [hs, GGQTwo.carrier_L_range e ib φ, ← hAL]
      rw [ggResQTwoResidual_L_order hCartL hshape hCe fL]
      rw [GGQTwo.LOrder_eq]
      simp only [Bool.not_eq_true] at hA
      rw [hA]
      rfl
  have hcoords : ∀ (i : Fin 4) (v : V),
      coord (ggLin (p := 3) ι (φ (π i)) v) = GGQTwo.refl r.C i (coord v) := by
    intro i v
    rw [hrefl (π i) v, map_sub, map_smul, coord_h i, alpha_coord i v]
    rfl
  have hminus : ¬ ∃ U : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) U = 2 ∧ ∀ u ∈ U, Q u = 0 := by
    rintro ⟨U, hU, hzero⟩
    apply hQnp
    refine ⟨U, ?_, hzero⟩
    rw [hU, hdim]
  exact GGQTwo.actualJoin_ggIsGOFourMinusThree_of_generators ι Q coord r hr
    hcardBs hQnd hdim hminus (fun _ => rfl) hinv gen hSA hScard
    (fun i => hcoords i.1)
    ⟨φ (π (GGQTwo.extra r.tag)), by
      rw [hAeq]
      exact Subgroup.subset_closure ⟨π (GGQTwo.extra r.tag), rfl⟩,
      hcoords (GGQTwo.extra r.tag)⟩

end CFSG.StandardType
