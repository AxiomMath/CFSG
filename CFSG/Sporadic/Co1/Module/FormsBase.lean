
module

public import CFSG.Sporadic.Co1.Module.OrbitsBase
public import CFSG.Sporadic.Co1.Module.FormsInputs
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public meta import Certificates.Data.CFSGNative.Co1.Data

@[expose] public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

theorem rowsMatrix_addRows (X Y : Array ℕ) :
    rowsMatrix 24 (addRows X Y) = rowsMatrix 24 X + rowsMatrix 24 Y := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold addRows
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_xor]
  rfl

@[expose] def letterMat (b : Bool) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  if b then matA else matB

@[expose] def wordMat (w : List Bool) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  (w.map letterMat).prod

theorem rowsMatrix_letterRows (b : Bool) : rowsMatrix 24 (letterRows b) = letterMat b := by
  cases b <;> rfl

theorem rowsMatrix_wordRows (w : List Bool) : rowsMatrix 24 (wordRows w) = wordMat w := by
  have key : ∀ (w : List Bool) (acc : Array ℕ),
      rowsMatrix 24 (w.foldl (fun acc b => mulRows 24 acc (letterRows b)) acc) =
        rowsMatrix 24 acc * wordMat w := by
    intro w
    induction w with
    | nil => intro acc; simp [wordMat]
    | cons b w ih =>
      intro acc
      rw [List.foldl_cons, ih, rowsMatrix_mulRows, rowsMatrix_letterRows, Matrix.mul_assoc]
      simp [wordMat]
  rw [wordRows, key, rowsMatrix_idRows, Matrix.one_mul]

@[expose] def Qm : Matrix (Fin 24) (Fin 24) (ZMod 2) := rowsMatrix 24 qRows

@[expose] def F₀ : Matrix (Fin 24) (Fin 24) (ZMod 2) := Qm + Qmᵀ

@[expose] def F₀inv : Matrix (Fin 24) (Fin 24) (ZMod 2) := rowsMatrix 24 f0InvRows

@[expose] def q₀ (v : Vec24) : ZMod 2 := v ⬝ᵥ (Qm *ᵥ v)

@[expose] def polar (q : Vec24 → ZMod 2) (u v : Vec24) : ZMod 2 := q (u + v) - q u - q v

theorem rowsMatrix_f0Rows : rowsMatrix 24 f0Rows = F₀ := by
  rw [f0Rows, rowsMatrix_addRows, rowsMatrix_transposeRows]
  rfl

theorem projRows_mulVec (u : Vec24) :
    rowsMatrix 24 projRows *ᵥ u = fun i => if i = 1 then 0 else u i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rowsMatrix_apply, projRows, Array.getElem?_ofFn, i.isLt,
    ↓reduceDIte, Option.getD_some]
  by_cases hi : i = 1
  · simp [hi, toVecD_zero]
  · have h1 : (i : ℕ) ≠ 1 := fun h => hi (Fin.ext h)
    simp [h1, hi, Nat.one_shiftLeft, toVecD_two_pow, Pi.single_apply]

theorem lamRows_vecMul (y : Vec24) :
    y ᵥ* rowsMatrix 24 lamRows = fun k => y k + y 13 * toVecD 24 10379264 k := by
  funext k
  simp only [Matrix.vecMul, dotProduct, rowsMatrix_apply, lamRows, Array.getElem?_ofFn,
    Fin.is_lt, ↓reduceDIte, Option.getD_some]
  simp only [toVecD_xor, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ x : Fin 24, y x * toVecD 24 (1 <<< (x : ℕ)) k = y k := by
    simp [Nat.one_shiftLeft, toVecD_two_pow, Pi.single_apply]
  have h2 : ∑ x : Fin 24, y x * toVecD 24 (if (x : ℕ) = 13 then 10379264 else 0) k =
      y 13 * toVecD 24 10379264 k := by
    rw [Finset.sum_eq_single (13 : Fin 24)]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ 13 := fun h => hb (Fin.ext h)
      simp [this, toVecD_zero]
    · simp
  rw [h1, h2]

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem vec_add_self (u : Vec24) : u + u = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (u i)

theorem commute_wordMat {N : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hA : matA * N = N * matA)
    (hB : matB * N = N * matB) (w : List Bool) : wordMat w * N = N * wordMat w := by
  induction w with
  | nil => simp [wordMat]
  | cons b w ih =>
    have hb : letterMat b * N = N * letterMat b := by
      cases b
      · exact hB
      · exact hA
    have : wordMat (b :: w) = letterMat b * wordMat w := by simp [wordMat]
    rw [this, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hb, Matrix.mul_assoc]

section Generic

variable {D : VecData} (hD : BaseFacts D)
include hD

theorem commute_J_gen {N : Matrix (Fin D.d) (Fin D.d) (ZMod 2)} (hA : mA D * N = N * mA D)
    (hB : mB D * N = N * mB D) {g : GL (Fin D.d) (ZMod 2)} (hg : g ∈ SmallF2.J D) :
    (g : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) * N =
      N * (g : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · have h : ((gA D : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = mA D :=
        a_val hD
      rw [h]
      exact hA
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have h : ((gB D : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = mB D :=
        b_val hD
      rw [h]
      exact hB
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]
  | inv x _ hx =>
    have h1 : ((x⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *
        (x : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = 1 := Units.inv_mul x
    have h2 : (x : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *
        ((x⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = 1 :=
      Units.mul_inv x
    calc ((x⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) * N
        = ((x⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) * (N * 1) := by
          rw [Matrix.mul_one]
      _ = ((x⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *
          (N * ((x : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *
            ((x⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)))) := by
          rw [h2]
      _ = ((x⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *
          ((N * (x : Matrix (Fin D.d) (Fin D.d) (ZMod 2))) *
            ((x⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2))) := by
          rw [Matrix.mul_assoc]
      _ = N * ((x⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) := by
          rw [← hx, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end Generic

theorem commute_Jmat
    {N : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hA : matA * N = N * matA)
    (hB : matB * N = N * matB) {g : GL (Fin 24) (ZMod 2)} (hg : g ∈ Jmat) :
    (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) * N = N * (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  let N' : Matrix (Fin dat.d) (Fin dat.d) (ZMod 2) := N
  have hA' : mA dat * N' = N' * mA dat := by
    rw [← rowsMatrix_rowsA]
    exact hA
  have hB' : mB dat * N' = N' * mB dat := by
    rw [← rowsMatrix_rowsB]
    exact hB
  exact commute_J_gen co1BaseFacts hA' hB' hg

theorem basis_inv_mul :
    rowsMatrix 24 dat.basisInv * rowsMatrix 24 (basisRows dat) = 1 := by
  have h := congrArg (rowsMatrix dat.d) co1BaseFacts.basis_inv
  rw [rowsMatrix_mulRows, rowsMatrix_idRows] at h
  exact h

theorem commute_of_inv {R : Type*} [Ring R] {S S' T F₀ F₀inv F : R} (hSS' : S * S' = 1)
    (hF₀ : T * F₀ * S = F₀) (hF : T * F * S = F) (hi : F₀inv * F₀ = 1)
    (hi' : F₀ * F₀inv = 1) : S' * (F₀inv * F) = (F₀inv * F) * S' := by
  have h1 : T * F₀ = F₀ * S' := by
    calc T * F₀ = T * F₀ * (S * S') := by rw [hSS', mul_one]
      _ = (T * F₀ * S) * S' := by rw [mul_assoc (T * F₀) S S']
      _ = F₀ * S' := by rw [hF₀]
  have h2 : T * F = F * S' := by
    calc T * F = T * F * (S * S') := by rw [hSS', mul_one]
      _ = (T * F * S) * S' := by rw [mul_assoc (T * F) S S']
      _ = F * S' := by rw [hF]
  have h3 : F₀inv * T = S' * F₀inv := by
    calc F₀inv * T = F₀inv * T * (F₀ * F₀inv) := by rw [hi', mul_one]
      _ = F₀inv * (T * F₀) * F₀inv := by simp only [mul_assoc]
      _ = F₀inv * (F₀ * S') * F₀inv := by rw [h1]
      _ = (F₀inv * F₀) * S' * F₀inv := by simp only [mul_assoc]
      _ = S' * F₀inv := by rw [hi, one_mul]
  calc S' * (F₀inv * F) = (S' * F₀inv) * F := by rw [mul_assoc]
    _ = (F₀inv * T) * F := by rw [h3]
    _ = F₀inv * (T * F) := by rw [mul_assoc]
    _ = F₀inv * (F * S') := by rw [h2]
    _ = (F₀inv * F) * S' := by rw [mul_assoc]

theorem additive_expand {f : Vec24 → ZMod 2} (hf : ∀ u v, f (u + v) = f u + f v) (v : Vec24) :
    f v = ∑ j, v j * f (Pi.single j 1) := by
  have h0 : f 0 = 0 := by
    have := hf 0 0
    simpa using this
  let g : Vec24 →+ ZMod 2 := AddMonoidHom.mk' f hf
  calc f v = g (∑ j, Pi.single j (v j)) := by rw [Finset.univ_sum_single]; rfl
    _ = ∑ j, g (Pi.single j (v j)) := map_sum g _ _
    _ = ∑ j, v j * f (Pi.single j 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rcases zmod2_cases (v j) with h | h
        · rw [h]
          simp [h0, g]
        · rw [h]
          simp [g]

theorem biadditive_expand {B : Vec24 → Vec24 → ZMod 2}
    (h1 : ∀ u u' v, B (u + u') v = B u v + B u' v) (h2 : ∀ u v v', B u (v + v') = B u v + B u v')
    (u v : Vec24) : B u v = ∑ i, ∑ j, u i * v j * B (Pi.single i 1) (Pi.single j 1) := by
  rw [additive_expand (f := fun u => B u v) (fun u u' => h1 u u' v) u]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [additive_expand (f := fun v => B (Pi.single i 1) v) (fun v v' => h2 _ v v') v,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dot_conj (M F : Matrix (Fin 24) (Fin 24) (ZMod 2)) (x y : Vec24) :
    (M *ᵥ x) ⬝ᵥ (F *ᵥ (M *ᵥ y)) = x ⬝ᵥ ((Mᵀ * F * M) *ᵥ y) := by
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem single_dot_mulVec_single (X : Matrix (Fin 24) (Fin 24) (ZMod 2)) (i j : Fin 24) :
    Pi.single i (1 : ZMod 2) ⬝ᵥ (X *ᵥ Pi.single j 1) = X i j := by
  simp

@[expose] def bil₀ (u v : Vec24) : ZMod 2 := u ⬝ᵥ (F₀ *ᵥ v)

theorem vecMul_wordMat {y : Vec24} (hA : y ᵥ* matA = y) (hB : y ᵥ* matB = y) (w : List Bool) :
    y ᵥ* wordMat w = y := by
  induction w with
  | nil => simp [wordMat]
  | cons b w ih =>
    have hb : y ᵥ* letterMat b = y := by
      cases b
      · exact hB
      · exact hA
    have : wordMat (b :: w) = letterMat b * wordMat w := by simp [wordMat]
    rw [this, ← Matrix.vecMul_vecMul, hb, ih]

theorem q₀_add (u v : Vec24) : q₀ (u + v) = q₀ u + q₀ v + bil₀ u v := by
  have hT : v ⬝ᵥ (Qm *ᵥ u) = u ⬝ᵥ (Qmᵀ *ᵥ v) := (Matrix.dotProduct_transpose_mulVec Qm u v).symm
  unfold q₀ bil₀ F₀
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, Matrix.add_mulVec,
    dotProduct_add, hT]
  ring

theorem q₀_zero : q₀ 0 = 0 := by simp [q₀]

theorem q₀_single (i : Fin 24) : q₀ (Pi.single i 1) = Qm i i := by
  unfold q₀
  exact single_dot_mulVec_single Qm i i

theorem q₀_invariant_gen {M : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hM : Mᵀ * F₀ * M = F₀)
    (hd : ∀ i, (Mᵀ * Qm * M) i i = Qm i i) (v : Vec24) : q₀ (M *ᵥ v) = q₀ v := by
  have hadd : ∀ u v, (q₀ (M *ᵥ (u + v)) + q₀ (u + v)) =
      (q₀ (M *ᵥ u) + q₀ u) + (q₀ (M *ᵥ v) + q₀ v) := by
    intro u v
    have hb : bil₀ (M *ᵥ u) (M *ᵥ v) = bil₀ u v := by
      unfold bil₀
      rw [dot_conj, hM]
    rw [Matrix.mulVec_add, q₀_add, q₀_add, hb]
    have h2 : bil₀ u v + bil₀ u v = 0 := CharTwo.add_self_eq_zero _
    linear_combination h2
  have hbasis : ∀ i, q₀ (M *ᵥ Pi.single i 1) + q₀ (Pi.single i 1) = 0 := by
    intro i
    have : q₀ (M *ᵥ Pi.single i 1) = (Mᵀ * Qm * M) i i := by
      unfold q₀
      rw [dot_conj]
      exact single_dot_mulVec_single _ i i
    rw [this, hd i, q₀_single]
    exact CharTwo.add_self_eq_zero _
  have h := additive_expand (f := fun v => q₀ (M *ᵥ v) + q₀ v) hadd v
  simp only [hbasis, mul_zero, Finset.sum_const_zero] at h
  have h' : q₀ (M *ᵥ v) = - q₀ v := eq_neg_of_add_eq_zero_left h
  rw [h']
  exact CharTwo.neg_eq _

theorem polar_comm (q : Vec24 → ZMod 2) (u v : Vec24) : polar q u v = polar q v u := by
  unfold polar
  rw [add_comm u v]
  ring

section Generic

variable {D : VecData} (hD : BaseFacts D)
include hD

theorem invariant_J_gen {X : Type*} {f : (Fin D.d → ZMod 2) → X}
    (hA : ∀ v, f (mA D *ᵥ v) = f v) (hB : ∀ v, f (mB D *ᵥ v) = f v)
    {g : GL (Fin D.d) (ZMod 2)} (hg : g ∈ SmallF2.J D) (v : Fin D.d → ZMod 2) :
    f ((g : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *ᵥ v) = f v := by
  induction hg using Subgroup.closure_induction generalizing v with
  | mem x hx =>
    rcases hx with rfl | hx
    · have h : ((gA D : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = mA D :=
        a_val hD
      rw [h]
      exact hA v
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have h : ((gB D : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = mB D :=
        b_val hD
      rw [h]
      exact hB v
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    have := hx (((x⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

end Generic

theorem invariant_Jmat
    {X : Type*} {f : Vec24 → X} (hA : ∀ v, f (matA *ᵥ v) = f v)
    (hB : ∀ v, f (matB *ᵥ v) = f v) (g : Jmat) (v : Vec24) : f (g • v) = f v := by
  have hA' : ∀ v : Fin dat.d → ZMod 2, f (mA dat *ᵥ v) = f v := by
    intro v
    rw [← rowsMatrix_rowsA]
    exact hA v
  have hB' : ∀ v : Fin dat.d → ZMod 2, f (mB dat *ᵥ v) = f v := by
    intro v
    rw [← rowsMatrix_rowsB]
    exact hB v
  rw [smul_eq_mulVec]
  exact invariant_J_gen co1BaseFacts hA' hB' g.2 v

theorem matrix_ext_mulVec {X Y : Matrix (Fin 24) (Fin 24) (ZMod 2)}
    (h : ∀ v, X *ᵥ v = Y *ᵥ v) : X = Y := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem toQuadraticForm'_apply (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) (x : Vec24) :
    Matrix.toQuadraticForm' M x = x ⬝ᵥ (M *ᵥ x) := by
  unfold Matrix.toQuadraticForm'
  simp [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', dotProduct,
    Matrix.mulVec, Finset.mul_sum]

noncomputable def q₀Form : QuadraticForm (ZMod 2) (Fin 24 → ZMod 2) := Matrix.toQuadraticForm' Qm

theorem q₀Form_apply (v : Vec24) : q₀Form v = q₀ v := toQuadraticForm'_apply Qm v

theorem polar_add_left_form (Q : QuadraticForm (ZMod 2) (Fin 24 → ZMod 2)) (u u' v : Vec24) :
    polar (fun x => Q x) (u + u') v = polar (fun x => Q x) u v + polar (fun x => Q x) u' v := by
  obtain ⟨B, hB⟩ := Q.exists_companion
  have hp : ∀ x y, polar (fun x => Q x) x y = B x y := by
    intro x y
    simp only [polar]
    rw [hB]
    ring
  rw [hp, hp, hp, map_add, LinearMap.add_apply]

theorem invariant_gen_of_Jmat {X : Type*} {f : Vec24 → X}
    (hinv : ∀ (g : Jmat) (v : Vec24), f (g • v) = f v) :
    (∀ v, f (matA *ᵥ v) = f v) ∧ (∀ v, f (matB *ᵥ v) = f v) := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · have := hinv genA v
    rwa [smul_eq_mulVec, genA_val] at this
  · have := hinv genB v
    rwa [smul_eq_mulVec, genB_val] at this

theorem invariant_gen_of_Co1 {X : Type*} {f : Vec24 → X}
    (hinv : ∀ (g : NativeSporadic.Co1) (v : Vec24), f (co1Act g v) = f v) :
    (∀ v, f (matA *ᵥ v) = f v) ∧ (∀ v, f (matB *ᵥ v) = f v) := by
  obtain ⟨a, ha⟩ := exists_co1_matA
  obtain ⟨b, hb⟩ := exists_co1_matB
  refine ⟨fun v => ?_, fun v => ?_⟩
  · have := hinv a v
    rwa [co1Act, ha] at this
  · have := hinv b v
    rwa [co1Act, hb] at this

theorem F₀_transpose : F₀ᵀ = F₀ := by
  unfold F₀
  rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

theorem F₀_diag (i : Fin 24) : F₀ i i = 0 := by
  unfold F₀
  rw [Matrix.add_apply, Matrix.transpose_apply]
  exact CharTwo.add_self_eq_zero _

theorem bil₀_comm (u v : Vec24) : bil₀ u v = bil₀ v u := by
  unfold bil₀
  rw [← Matrix.dotProduct_transpose_mulVec, F₀_transpose]

theorem bil₀_self (v : Vec24) : bil₀ v v = 0 := by
  have h := q₀_add v v
  rw [vec_add_self, q₀_zero] at h
  have h2 : q₀ v + q₀ v = 0 := CharTwo.add_self_eq_zero _
  linear_combination -h - h2

theorem polar_q₀ (u v : Vec24) : polar q₀ u v = bil₀ u v := by
  unfold polar
  rw [q₀_add]
  ring

theorem q₀_polar_add_left (u u' v : Vec24) :
    polar q₀ (u + u') v = polar q₀ u v + polar q₀ u' v := by
  rw [polar_q₀, polar_q₀, polar_q₀]
  unfold bil₀
  rw [add_dotProduct]

end CFSG.Sporadic.Co1.Module
