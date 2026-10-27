module

public import CFSG.Quasithin.H13.A6S13821L32HatLemmaM
public import CFSG.Quasithin.H13.A6S13821L32HatOut

public section

namespace CFSG.Quasithin.H13.A6.L32HatC2

open CFSG.Quasithin.H13.A6.L32HatM

abbrev SX1 : Subgroup SL3 := CFSG.Quasithin.H13.A6.SL3.X1

abbrev SX2 : Subgroup SL3 := CFSG.Quasithin.H13.A6.SL3.X2

def adjM (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![M 1 1 * M 2 2 - M 1 2 * M 2 1, -(M 0 1 * M 2 2) + M 0 2 * M 2 1,
      M 0 1 * M 1 2 - M 0 2 * M 1 1;
    -(M 1 0 * M 2 2) + M 1 2 * M 2 0, M 0 0 * M 2 2 - M 0 2 * M 2 0,
      -(M 0 0 * M 1 2) + M 0 2 * M 1 0;
    M 1 0 * M 2 1 - M 1 1 * M 2 0, -(M 0 0 * M 2 1) + M 0 1 * M 2 0,
      M 0 0 * M 1 1 - M 0 1 * M 1 0]

theorem adjM_eq (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : adjM M = Matrix.adjugate M := by
  rw [Matrix.adjugate_fin_three]; rfl

theorem inv_val (A : SL3) : (A⁻¹ : SL3).1 = adjM A.1 := by
  rw [adjM_eq]
  rfl

def w0M : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

def w0 : SL3 := ⟨w0M, by rw [Matrix.det_fin_three]; decide +kernel⟩

def thetaM (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  w0M * Matrix.transpose (adjM M) * w0M

noncomputable def theta : SL3 ≃* SL3 :=
  L32HatOut.tauE.trans (MulAut.conj w0)

theorem adjM_w0M : adjM w0M = w0M := by decide +kernel

theorem theta_val (A : SL3) : (theta A).1 = thetaM A.1 := by
  have h1 : (L32HatOut.tauE A).1 = Matrix.transpose (adjM A.1) := by
    change Matrix.transpose (Matrix.adjugate A.1) = _
    rw [adjM_eq]
  have h2 : (w0⁻¹ : SL3).1 = w0M := by
    rw [inv_val]
    exact adjM_w0M
  show (w0 * L32HatOut.tauE A * w0⁻¹).1 = _
  have e : (w0 * L32HatOut.tauE A * w0⁻¹).1 = w0.1 * (L32HatOut.tauE A).1 * (w0⁻¹).1 := rfl
  rw [e, h2, h1]
  rfl

theorem theta_core : ∀ A : SL3, (thetaM A.1 1 0 = 0 ∧ thetaM A.1 2 0 = 0) ↔
    (A.1 2 0 = 0 ∧ A.1 2 1 = 0) := by
  decide +kernel

theorem theta_core' : ∀ A : SL3, (A.1 1 0 = 0 ∧ A.1 2 0 = 0) ↔
    (thetaM A.1 2 0 = 0 ∧ thetaM A.1 2 1 = 0) := by
  decide +kernel

theorem theta_mem_X1 (A : SL3) : theta A ∈ SX1 ↔ A ∈ SX2 := by
  show (theta A).1 1 0 = 0 ∧ (theta A).1 2 0 = 0 ↔ A.1 2 0 = 0 ∧ A.1 2 1 = 0
  rw [theta_val]
  exact theta_core A

theorem theta_mem_X2 (A : SL3) : theta A ∈ SX2 ↔ A ∈ SX1 := by
  show (theta A).1 2 0 = 0 ∧ (theta A).1 2 1 = 0 ↔ A.1 1 0 = 0 ∧ A.1 2 0 = 0
  rw [theta_val]
  exact (theta_core' A).symm

def invM (A : SL3) : SL3 := ⟨adjM A.1, by
  rw [adjM_eq, Matrix.det_adjugate, A.2, one_pow]⟩

theorem inv_eq_invM (A : SL3) : A⁻¹ = invM A := Subtype.ext (inv_val A)

theorem ela₁_mul_ela₁ : ela₁ * ela₁ = 1 := by decide +kernel

theorem ela₂_mul_ela₂ : ela₂ * ela₂ = 1 := by decide +kernel

theorem ela₁_mul_ela₂_comm : ela₁ * ela₂ = ela₂ * ela₁ := by decide +kernel

theorem mem_E0_iff (e : SL3) : e ∈ E₀ ↔ e = 1 ∨ e = ela₁ ∨ e = ela₂ ∨ e = ela₁ * ela₂ := by
  constructor
  · intro he
    have he' : e ∈ Subgroup.closure ({ela₁, ela₂} : Set SL3) := he
    clear he
    induction he' using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide +kernel
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ela₁_mul_ela₁))
      · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ela₂_mul_ela₂)))
      · exact Or.inr (Or.inr (Or.inr (by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ela₁_mul_ela₁,
            inv_eq_of_mul_eq_one_right ela₂_mul_ela₂, ela₁_mul_ela₂_comm])))
  · rintro (rfl | rfl | rfl | rfl)
    · exact E₀.one_mem
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact E₀.mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem E0_le_X1 : E₀ ≤ SX1 := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl)
  · show (ela₁ : SL3).1 1 0 = 0 ∧ (ela₁ : SL3).1 2 0 = 0
    decide +kernel
  · show (ela₂ : SL3).1 1 0 = 0 ∧ (ela₂ : SL3).1 2 0 = 0
    decide +kernel

theorem E0_conj_ela₁ : ∀ A : SL3, (A.1 1 0 = 0 ∧ A.1 2 0 = 0) →
    A * ela₁ * invM A = 1 ∨ A * ela₁ * invM A = ela₁ ∨ A * ela₁ * invM A = ela₂ ∨
      A * ela₁ * invM A = ela₁ * ela₂ := by
  decide +kernel

theorem E0_conj_ela₂ : ∀ A : SL3, (A.1 1 0 = 0 ∧ A.1 2 0 = 0) →
    A * ela₂ * invM A = 1 ∨ A * ela₂ * invM A = ela₁ ∨ A * ela₂ * invM A = ela₂ ∨
      A * ela₂ * invM A = ela₁ * ela₂ := by
  decide +kernel

theorem conj_gen_mem {g : SL3} (hg : g ∈ SX1) {x : SL3} (hx : x = ela₁ ∨ x = ela₂) :
    g * x * g⁻¹ ∈ E₀ := by
  have hg' : g.1 1 0 = 0 ∧ g.1 2 0 = 0 := hg
  rw [inv_eq_invM, mem_E0_iff]
  rcases hx with rfl | rfl
  · rcases E0_conj_ela₁ g hg' with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases E0_conj_ela₂ g hg' with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem E0_normal_X1 {g : SL3} (hg : g ∈ SX1) {e : SL3} (he : e ∈ E₀) :
    g * e * g⁻¹ ∈ E₀ := by
  have he' : e ∈ Subgroup.closure ({ela₁, ela₂} : Set SL3) := he
  clear he
  induction he' using Subgroup.closure_induction with
  | mem x hx => exact conj_gen_mem hg hx
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact E₀.mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact E₀.inv_mem hx

theorem E0_sq {e : SL3} (he : e ∈ E₀) : e ^ 2 = 1 := by
  rcases (mem_E0_iff e).1 he with rfl | rfl | rfl | rfl
  · simp
  · rw [sq]; exact ela₁_mul_ela₁
  · rw [sq]; exact ela₂_mul_ela₂
  · decide +kernel

theorem odd_of_pow_three {x : SL3} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : Odd (orderOf x) := by
  rw [orderOf_eq_prime h3 h1]
  decide +kernel

theorem rho₃_mem_X1 : rho₃ ∈ SX1 := by
  show (rho₃ : SL3).1 1 0 = 0 ∧ (rho₃ : SL3).1 2 0 = 0
  decide +kernel

theorem rho₃_odd : Odd (orderOf rho₃) :=
  odd_of_pow_three (by decide +kernel) (by decide +kernel)

def y1 : SL3 := ⟨!![1, 1, 0; 0, 1, 1; 0, 1, 0], by rw [Matrix.det_fin_three]; decide +kernel⟩

def z2 : SL3 := ⟨!![1, 0, 1; 0, 1, 1; 0, 1, 0], by rw [Matrix.det_fin_three]; decide +kernel⟩

theorem ela₁_eq : ela₁ = rho₃ * y1 := by decide +kernel

theorem ela₂_eq : ela₂ = rho₃ * z2 := by decide +kernel

theorem y1_odd : Odd (orderOf y1) := odd_of_pow_three (by decide +kernel) (by decide +kernel)

theorem z2_odd : Odd (orderOf z2) := odd_of_pow_three (by decide +kernel) (by decide +kernel)

theorem y1_mem_X1 : y1 ∈ SX1 := by
  show (y1 : SL3).1 1 0 = 0 ∧ (y1 : SL3).1 2 0 = 0
  decide +kernel

theorem z2_mem_X1 : z2 ∈ SX1 := by
  show (z2 : SL3).1 1 0 = 0 ∧ (z2 : SL3).1 2 0 = 0
  decide +kernel

theorem A0_le_oTwoUpper_X1 : A₀ ≤ oTwoUpper SX1 := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x (rfl | rfl | rfl)
  · rw [ela₁_eq]
    exact (oTwoUpper SX1).mul_mem (Subgroup.subset_closure ⟨rho₃_mem_X1, rho₃_odd⟩)
      (Subgroup.subset_closure ⟨y1_mem_X1, y1_odd⟩)
  · rw [ela₂_eq]
    exact (oTwoUpper SX1).mul_mem (Subgroup.subset_closure ⟨rho₃_mem_X1, rho₃_odd⟩)
      (Subgroup.subset_closure ⟨z2_mem_X1, z2_odd⟩)
  · exact Subgroup.subset_closure ⟨rho₃_mem_X1, rho₃_odd⟩

end CFSG.Quasithin.H13.A6.L32HatC2
