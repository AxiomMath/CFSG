module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneRestSp

public section

namespace CFSG.StandardType

namespace WitSpNs

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

@[expose] def plane : Fin n ⊕ Fin n → Fin n := Sum.elim id id

@[expose] def side : Fin n ⊕ Fin n → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

@[simp] theorem plane_inl (j : Fin n) : plane (Sum.inl j : Fin n ⊕ Fin n) = j := rfl

@[simp] theorem plane_inr (j : Fin n) : plane (Sum.inr j : Fin n ⊕ Fin n) = j := rfl

@[simp] theorem side_inl (j : Fin n) : side (Sum.inl j : Fin n ⊕ Fin n) = 0 := rfl

@[simp] theorem side_inr (j : Fin n) : side (Sum.inr j : Fin n ⊕ Fin n) = 1 := rfl

@[expose] def coord (a : Fin 2) (j : Fin n) : Fin n ⊕ Fin n :=
  if a = 0 then Sum.inl j else Sum.inr j

@[simp] theorem plane_coord (a : Fin 2) (j : Fin n) : plane (coord a j) = j := by
  unfold coord
  split_ifs <;> rfl

@[simp] theorem side_coord (a : Fin 2) (j : Fin n) : side (coord a j) = a := by
  unfold coord
  split_ifs with h
  · exact h.symm
  · fin_cases a
    · exact absurd rfl h
    · rfl

theorem eq_of_plane_side {a b : Fin n ⊕ Fin n} (hp : plane a = plane b) (hs : side a = side b) :
    a = b := by
  rcases a with i | i <;> rcases b with j | j
  · rw [show i = j from hp]
  · simp at hs
  · simp at hs
  · rw [show i = j from hp]

@[expose] def planeMat (M : Fin n → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.of fun a b => if plane a = plane b then M (plane b) (side a) (side b) else 0

theorem planeMat_apply (M : Fin n → Matrix (Fin 2) (Fin 2) K) (a b : Fin n ⊕ Fin n) :
    planeMat M a b = if plane a = plane b then M (plane b) (side a) (side b) else 0 := rfl

theorem planeMat_one : planeMat (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) =
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
  ext a b
  rw [planeMat_apply]
  rcases a with i | i <;> rcases b with j | j <;> by_cases hij : i = j <;>
    simp [hij, Matrix.one_apply]

theorem planeMat_coord (M : Fin n → Matrix (Fin 2) (Fin 2) K) (j : Fin n) (a b : Fin 2) :
    planeMat M (coord a j) (coord b j) = M j a b := by
  rw [planeMat_apply, ite_eq_left (by simp), plane_coord, side_coord, side_coord]

theorem planeMat_injective : Function.Injective (planeMat (K := K) (n := n)) := by
  intro M M' h
  funext j
  ext a b
  rw [← planeMat_coord M j a b, ← planeMat_coord M' j a b, h]

theorem planeMat_mulVec_inl (M : Fin n → Matrix (Fin 2) (Fin 2) K) (j : Fin n) :
    planeMat M *ᵥ Pi.single (Sum.inl j) 1 =
      M j 0 0 • Pi.single (Sum.inl j) 1 + M j 1 0 • Pi.single (Sum.inr j) 1 := by
  funext a
  rw [mulVec_single_one_apply, planeMat_apply]
  rcases a with i | i <;> by_cases hij : i = j <;> simp [hij]

theorem planeMat_mulVec_inr (M : Fin n → Matrix (Fin 2) (Fin 2) K) (j : Fin n) :
    planeMat M *ᵥ Pi.single (Sum.inr j) 1 =
      M j 0 1 • Pi.single (Sum.inl j) 1 + M j 1 1 • Pi.single (Sum.inr j) 1 := by
  funext a
  rw [mulVec_single_one_apply, planeMat_apply]
  rcases a with i | i <;> by_cases hij : i = j <;> simp [hij]

theorem eq_planeMat_of_mulVec {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    {M : Fin n → Matrix (Fin 2) (Fin 2) K}
    (h₁ : ∀ j, A *ᵥ Pi.single (Sum.inl j) 1 =
      M j 0 0 • Pi.single (Sum.inl j) 1 + M j 1 0 • Pi.single (Sum.inr j) 1)
    (h₂ : ∀ j, A *ᵥ Pi.single (Sum.inr j) 1 =
      M j 0 1 • Pi.single (Sum.inl j) 1 + M j 1 1 • Pi.single (Sum.inr j) 1) :
    A = planeMat M := by
  ext a b
  rcases b with j | j
  · rw [← mulVec_single_one_apply A, h₁, ← planeMat_mulVec_inl, mulVec_single_one_apply]
  · rw [← mulVec_single_one_apply A, h₂, ← planeMat_mulVec_inr, mulVec_single_one_apply]

theorem planeMat_mul (M M' : Fin n → Matrix (Fin 2) (Fin 2) K) :
    planeMat M * planeMat M' = planeMat fun j => M j * M' j := by
  refine eq_planeMat_of_mulVec (fun j => ?_) (fun j => ?_)
  · rw [← Matrix.mulVec_mulVec, planeMat_mulVec_inl, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, planeMat_mulVec_inl, planeMat_mulVec_inr, Matrix.mul_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    module
  · rw [← Matrix.mulVec_mulVec, planeMat_mulVec_inr, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, planeMat_mulVec_inl, planeMat_mulVec_inr, Matrix.mul_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    module

theorem mat_longBlock_eq_planeMat (i : Fin n) (A : SL(2, K)) :
    mat n K (longBlock K n i A) =
      planeMat (Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) i
        (A : Matrix (Fin 2) (Fin 2) K)) := by
  ext a b
  rw [mat_longBlock, planeMat_apply]
  simp only [CFSG.LieType.Steinberg.Sp.blockMat, Matrix.of_apply]
  rcases a with a | a <;> rcases b with b | b <;> by_cases ha : a = i <;> by_cases hb : b = i <;>
    by_cases hab : a = b <;>
    simp_all [Matrix.one_apply]

@[expose] def epsPlane (π : Equiv.Perm (Fin n)) : Fin n ⊕ Fin n ≃ (Fin 2 × Fin n) ⊕ Fin 0 where
  toFun a := Sum.inl (side a, π (plane a))
  invFun z := Sum.elim (fun c => coord c.1 (π.symm c.2)) Fin.elim0 z
  left_inv a := by
    rcases a with j | j <;> simp [coord]
  right_inv z := by
    rcases z with ⟨c, b⟩ | z
    · simp
    · exact z.elim0

theorem epsPlane_apply (π : Equiv.Perm (Fin n)) (a : Fin n ⊕ Fin n) :
    epsPlane π a = Sum.inl (side a, π (plane a)) := rfl

theorem nsCore_submatrix_epsPlane (π : Equiv.Perm (Fin n)) (C : Matrix (Fin 2) (Fin 2) K)
    (k : Fin n → ℕ) :
    (SLNS.nsCore (r := 0) C k).submatrix (epsPlane π) (epsPlane π) =
      planeMat fun j => C ^ k (π j) := by
  ext a b
  rw [Matrix.submatrix_apply, epsPlane_apply, epsPlane_apply, planeMat_apply, SLNS.nsCore,
    Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply]
  dsimp only
  simp only [π.injective.eq_iff]
  split_ifs with h
  · rw [h]
  · rfl

theorem spBlockMat_of_planeMat (A₀ D : StatedSp n K) (π : Equiv.Perm (Fin n))
    (C : Matrix (Fin 2) (Fin 2) K) (k : Fin n → ℕ)
    (hD : mat n K D = planeMat fun j => C ^ k (π j)) :
    RootPlaneSp.SpBlockMat (A₀ : GL (Fin n ⊕ Fin n) K) (epsPlane π) C (A₀ * D * A₀⁻¹) k := by
  rw [RootPlaneSp.SpBlockMat, nsCore_submatrix_epsPlane, ← hD]
  show mat n K (A₀ * D * A₀⁻¹) = _
  rw [map_mul, map_mul]
  rfl

end WitSpNs

end CFSG.StandardType
