
module

public import CFSG.Sporadic.Schreier.J4SPrimesCheckBase
public import CFSG.Sporadic.Schreier.J4SGLBase
public import CFSG.Sporadic.Schreier.J4SFrattiniBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem bounded_getD {C : Array ℕ} (hC : Bounded C) : ∀ j < 11, C[j]?.getD 0 < 2 ^ 11 :=
  fun j hj => by rw [← getElem!_eq_getD']; exact hC.2 j hj

theorem bounded_comp11 {C D : Array ℕ} (hC : Bounded C) (hD : Bounded D) :
    Bounded (comp11 C D) := by
  refine ⟨by rw [comp11, mulRows, Array.size_map, hD.1], fun j hj => ?_⟩
  rw [comp11, mulRows, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem (by rw [hD.1]; exact hj), Option.map_some, Option.getD_some]
  exact vecMulN_lt (bounded_getD hC) _

def colsOf (k : J) : Array ℕ := by
  classical
  exact Array.ofFn (n := 11) fun j =>
    if h : ∃ a < 2048, η a = k * u j * k⁻¹ then Classical.choose h else 0

theorem signedWord_bWord {G : Type*} [Group G] (x y : G) :
    signedWord x y bWord = x * y * x * y * x * y⁻¹ * x * y⁻¹ := by
  simp only [signedWord, bWord, letter, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  norm_num [mul_assoc]

def bElt : J := signedWord x y bWord

def qElt : J := bElt ^ 48964608

theorem qElt_mem_K : qElt ∈ K := K.pow_mem (signedWord_mem_K _) _

def q7Elt : J := signedWord x y w7 ^ 2

theorem q7Elt_mem_K : q7Elt ∈ K := K.pow_mem (signedWord_mem_K _) _

def q23Elt : J := signedWord x y w23 ^ 10644480

theorem q23Elt_mem_K : q23Elt ∈ K := K.pow_mem (signedWord_mem_K _) _

theorem colsMatrix_powCols :
    ∀ (m : ℕ) (C : Array ℕ), colsMatrix (powCols C m) = colsMatrix C ^ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro C
    rw [powCols]
    by_cases hm : m = 0
    · rw [ite_eq_left hm, hm, pow_zero, colsMatrix_idRows]
    · rw [ite_eq_right hm]
      have e : colsMatrix C ^ m =
          colsMatrix C ^ (m % 2) * (colsMatrix C * colsMatrix C) ^ (m / 2) := by
        rw [← sq, ← pow_mul, ← pow_add, Nat.mod_add_div]
      by_cases ho : m % 2 = 1
      · rw [ite_eq_left ho, colsMatrix_comp11, ih _ (by omega), colsMatrix_comp11, e, ho, pow_one]
      · rw [ite_eq_right ho, ih _ (by omega), colsMatrix_comp11, e, show m % 2 = 0 by omega,
          pow_zero, one_mul]

theorem colsMatrix_mulVec_single (C : Array ℕ) (i : Fin 11) :
    colsMatrix C *ᵥ Pi.single i 1 = toVecD 11 (C[i.val]?.getD 0) := by
  rw [Matrix.mulVec_single_one]
  funext r
  rfl

theorem colsMatrix_inj {C D : Array ℕ} (hC : Bounded C) (hD : Bounded D)
    (h : colsMatrix C = colsMatrix D) : C = D := by
  refine Array.ext (by rw [hC.1, hD.1]) fun j h1 h2 => ?_
  have hj : j < 11 := hC.1 ▸ h1
  have e := congrArg (fun M => M *ᵥ Pi.single (⟨j, hj⟩ : Fin 11) 1) h
  rw [colsMatrix_mulVec_single, colsMatrix_mulVec_single] at e
  have := toVecD_injective (bounded_getD hC j hj) (bounded_getD hD j hj) e
  rwa [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at this

theorem matrix_eq_of_cols {M M' : Matrix (Fin 11) (Fin 11) (ZMod 2)}
    (h : ∀ i, M *ᵥ Pi.single i 1 = M' *ᵥ Pi.single i 1) : M = M' := by
  ext r i
  have := congrFun (h i) r
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this

end CFSG.Sporadic.J4Schreier
