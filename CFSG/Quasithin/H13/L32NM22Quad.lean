module

public import CFSG.Quasithin.H13.L32NItems1442Models
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.H13.M22Quad

open Matrix L1442M

variable {n : ℕ}

theorem quadOf_mulVec (Q γ : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    quadOf Q (γ *ᵥ x) = quadOf (γᵀ * Q * γ) x := by
  simp only [quadOf]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem quadOf_add (Q R : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    quadOf (Q + R) x = quadOf Q x + quadOf R x := by
  simp only [quadOf, Matrix.add_mulVec, dotProduct_add]

theorem quadOf_transpose (U : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    quadOf Uᵀ x = quadOf U x := by
  simp only [quadOf]
  rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]

theorem quadOf_alt (Q U : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    quadOf (Q + U + Uᵀ) x = quadOf Q x := by
  rw [quadOf_add, quadOf_add, quadOf_transpose, add_assoc, ← two_mul,
    show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

theorem quad_of_cong {Q γ U : Matrix (Fin n) (Fin n) (ZMod 2)} (h : γᵀ * Q * γ = Q + U + Uᵀ)
    (x : Fin n → ZMod 2) : quadOf Q (γ *ᵥ x) = quadOf Q x := by
  rw [quadOf_mulVec, h, quadOf_alt]

@[expose] noncomputable def polarN (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) :=
  Matrix.toLinearMap₂' (ZMod 2) (Q + Qᵀ)

theorem polarN_def (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (x y : Fin n → ZMod 2) :
    polarN Q x y = x ⬝ᵥ ((Q + Qᵀ) *ᵥ y) :=
  Matrix.toLinearMap₂'_apply' _ x y

theorem polarN_apply (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (x y : Fin n → ZMod 2) :
    polarN Q x y = quadOf Q (x + y) + quadOf Q x + quadOf Q y := by
  have hx := CharTwo.add_self_eq_zero (x ⬝ᵥ (Q *ᵥ x))
  have hy := CharTwo.add_self_eq_zero (y ⬝ᵥ (Q *ᵥ y))
  have e1 : x ⬝ᵥ (Qᵀ *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  simp only [polarN_def, quadOf, Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_add,
    add_dotProduct, e1]
  linear_combination -(hx + hy)

theorem polarN_sub_left (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (x x' y : Fin n → ZMod 2) :
    polarN Q (x - x') y = polarN Q x y - polarN Q x' y := by
  rw [polarN_def, polarN_def, polarN_def, sub_dotProduct]

theorem polarN_symm (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (x y : Fin n → ZMod 2) :
    polarN Q x y = polarN Q y x := by
  rw [polarN_apply, polarN_apply, add_comm x y]
  ring

theorem polarN_sep {Q Minv : Matrix (Fin n) (Fin n) (ZMod 2)} (hMinv : (Q + Qᵀ) * Minv = 1)
    {v : Fin n → ZMod 2} (h : ∀ u, polarN Q v u = 0) : v = 0 := by
  funext i
  have h1 := h (Minv *ᵥ Pi.single i 1)
  rw [polarN_def, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec, dotProduct_single,
    mul_one] at h1
  exact h1

theorem eq_quad_of_comm {S : Set (GL (Fin n) (ZMod 2))} {Q₀ Minv : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hinv₀ : ∀ g ∈ S, ∀ x, quadOf Q₀ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = quadOf Q₀ x)
    (hMinv : (Q₀ + Q₀ᵀ) * Minv = 1)
    (hcomm : ∀ A : Matrix (Fin n) (Fin n) (ZMod 2),
      (∀ g ∈ S, A * (g : Matrix (Fin n) (Fin n) (ZMod 2)) =
        (g : Matrix (Fin n) (Fin n) (ZMod 2)) * A) → A = 0 ∨ A = 1)
    (hcov : ∀ w : Fin n → ZMod 2,
      (∀ g ∈ S, (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ w = w) → w = 0)
    {Q' : (Fin n → ZMod 2) → ZMod 2} {B' : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2)}
    (hQ' : ∀ x y, Q' (x + y) = Q' x + Q' y + B' x y) (hB' : B' ≠ 0)
    (hinv' : ∀ g ∈ S, ∀ x, Q' ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = Q' x) :
    ∀ x, Q' x = quadOf Q₀ x := by
  classical
  have hB'inv : ∀ g ∈ S, ∀ x y,
      B' ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) =
        B' x y := by
    intro g hg x y
    have h1 := hQ' ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y)
    rw [← Matrix.mulVec_add, hinv' g hg, hinv' g hg, hinv' g hg, hQ' x y] at h1
    linear_combination -h1
  have hB₀inv : ∀ g ∈ S, ∀ x y,
      polarN Q₀ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)
        ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) = polarN Q₀ x y := by
    intro g hg x y
    rw [polarN_apply, polarN_apply, ← Matrix.mulVec_add, hinv₀ g hg, hinv₀ g hg, hinv₀ g hg]
  obtain ⟨M', hM'⟩ : ∃ M', M' = LinearMap.toMatrix₂' (ZMod 2) B' := ⟨_, rfl⟩
  have hB'mat : ∀ u v, B' u v = u ⬝ᵥ (M' *ᵥ v) := by
    intro u v
    have h1 : Matrix.toLinearMap₂' (ZMod 2) M' = B' := by
      rw [hM']
      exact (LinearMap.toMatrix₂' (ZMod 2)).symm_apply_apply B'
    rw [← Matrix.toLinearMap₂'_apply', h1]
  obtain ⟨Am, hAm⟩ : ∃ Am, Am = Minv * M' := ⟨_, rfl⟩
  have hsym : (Q₀ + Q₀ᵀ)ᵀ = Q₀ + Q₀ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hvm : ∀ u, ((Q₀ + Q₀ᵀ) *ᵥ u) ᵥ* Minv = u := by
    intro u
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hsym, hMinv, Matrix.vecMul_one]
  have hA : ∀ u v, polarN Q₀ (Am *ᵥ v) u = B' u v := by
    intro u v
    rw [polarN_def, dotProduct_comm, hAm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hvm,
      hB'mat]
  have hginv : ∀ g : GL (Fin n) (ZMod 2), ∀ u,
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ (((g⁻¹ : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) = u := by
    intro g u
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hAcomm : ∀ g ∈ S, ∀ v, Am *ᵥ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ (Am *ᵥ v) := by
    intro g hg v
    refine sub_eq_zero.mp (polarN_sep hMinv fun u => ?_)
    have h1 : polarN Q₀ (Am *ᵥ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v)) u =
        polarN Q₀ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ (Am *ᵥ v)) u := by
      rw [hA, ← hginv g u, hB'inv g hg, ← hA, ← hB₀inv g hg, hginv g u]
    rw [polarN_sub_left, h1, sub_self]
  have hAmcomm : ∀ g ∈ S, Am * (g : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * Am := by
    intro g hg
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hAcomm g hg]
  rcases hcomm Am hAmcomm with h0 | h1
  · exfalso
    apply hB'
    refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
    rw [← hA, h0, Matrix.zero_mulVec, map_zero]
    rfl
  have hB'p : ∀ x y, B' x y = polarN Q₀ y x := fun x y => by
    rw [← hA, h1, Matrix.one_mulVec]
  let ℓ : (Fin n → ZMod 2) →+ ZMod 2 :=
    { toFun := fun x => Q' x + quadOf Q₀ x
      map_zero' := by
        have h0 := hQ' 0 0
        have hb0 : B' 0 0 = 0 := by simp
        rw [add_zero, hb0, add_zero] at h0
        have hQ0 : Q' 0 = 0 := by linear_combination -h0
        simp [hQ0, quadOf]
      map_add' := fun x y => by
        have h2 := hB'p x y
        show Q' (x + y) + quadOf Q₀ (x + y) = Q' x + quadOf Q₀ x + (Q' y + quadOf Q₀ y)
        rw [hQ', h2, polarN_symm, polarN_apply]
        linear_combination CharTwo.add_self_eq_zero (quadOf Q₀ (x + y)) }
  have hℓ : ∀ x, ℓ x = Q' x + quadOf Q₀ x := fun x => rfl
  have hℓinv : ∀ g ∈ S, ∀ x, ℓ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ℓ x := by
    intro g hg x
    rw [hℓ, hℓ, hinv' g hg, hinv₀ g hg]
  set w : Fin n → ZMod 2 := fun i => ℓ (Pi.single i 1) with hw
  have hsmul : ∀ (c : ZMod 2) v, ℓ (c • v) = c * ℓ v := by
    intro c v
    fin_cases c
    · show ℓ ((0 : ZMod 2) • v) = (0 : ZMod 2) * ℓ v
      rw [zero_smul, map_zero, zero_mul]
    · show ℓ ((1 : ZMod 2) • v) = (1 : ZMod 2) * ℓ v
      rw [one_smul, one_mul]
  have hei : ∀ i : Fin n, (fun j => if i = j then (1 : ZMod 2) else 0) = Pi.single i 1 := by
    intro i
    funext j
    simp [Pi.single_apply, eq_comm]
  have hℓw : ∀ x, ℓ x = w ⬝ᵥ x := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, mul_comm, hei, hw]
  have hwfix : ∀ g ∈ S, (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ w = w := by
    intro g hg
    funext i
    have h1 := hℓinv g hg (Pi.single i 1)
    rw [hℓw, hℓw, Matrix.dotProduct_mulVec, dotProduct_single, mul_one,
      dotProduct_single, mul_one] at h1
    rw [← h1, Matrix.mulVec_transpose]
  have hw0 := hcov w hwfix
  intro x
  have h1 := hℓw x
  rw [hw0, zero_dotProduct, hℓ] at h1
  linear_combination h1 - CharTwo.add_self_eq_zero (quadOf Q₀ x)

@[expose] def m22aU : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def m22bU : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1;
    0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def q12Minv : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1;
    0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0]

theorem m22a_q12 : (m22a : Matrix (Fin 12) (Fin 12) (ZMod 2))ᵀ * q12 *
    (m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) = q12 + m22aU + m22aUᵀ := by decide +kernel

theorem m22b_q12 : (m22b : Matrix (Fin 12) (Fin 12) (ZMod 2))ᵀ * q12 *
    (m22b : Matrix (Fin 12) (Fin 12) (ZMod 2)) = q12 + m22bU + m22bUᵀ := by decide +kernel

theorem gram_inv : (q12 + q12ᵀ) * q12Minv = 1 := by decide +kernel

theorem quad_m22 : ∀ γ ∈ m22, ∀ x,
    quadOf q12 ((γ : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ x) = quadOf q12 x := by
  intro γ hγ
  unfold m22 at hγ
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact quad_of_cong m22a_q12
    · exact quad_of_cong m22b_q12
  | one => intro x; rw [Units.val_one, Matrix.one_mulVec]
  | mul a b _ _ ha hb => intro x; rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  | inv a _ ha =>
    intro x
    have h := ha (((a⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ x)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm

theorem cov_of_irr
    (hirr : ∀ J : Submodule (ZMod 2) (Fin 12 → ZMod 2),
      (∀ γ ∈ m22, ∀ v ∈ J, (γ : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v ∈ J) → J = ⊥ ∨ J = ⊤)
    (w : Fin 12 → ZMod 2) (hw : ∀ γ ∈ m22, (γ : Matrix (Fin 12) (Fin 12) (ZMod 2))ᵀ *ᵥ w = w) :
    w = 0 := by
  classical
  let J : Submodule (ZMod 2) (Fin 12 → ZMod 2) :=
    { carrier := {v | w ⬝ᵥ v = 0}
      add_mem' := fun {a b} ha hb => by
        show w ⬝ᵥ (a + b) = 0
        rw [dotProduct_add, show w ⬝ᵥ a = 0 from ha, show w ⬝ᵥ b = 0 from hb, add_zero]
      zero_mem' := by
        show w ⬝ᵥ 0 = 0
        rw [dotProduct_zero]
      smul_mem' := fun c v hv => by
        show w ⬝ᵥ (c • v) = 0
        rw [dotProduct_smul, show w ⬝ᵥ v = 0 from hv, smul_zero] }
  have hmem : ∀ v, v ∈ J ↔ w ⬝ᵥ v = 0 := fun v => Iff.rfl
  have hinv : ∀ γ ∈ m22, ∀ v ∈ J, (γ : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v ∈ J := by
    intro γ hγ v hv
    rw [hmem] at hv ⊢
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hw γ hγ, hv]
  have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  rcases hirr J hinv with hJ | hJ
  · exfalso
    have hbot : ∀ v, w ⬝ᵥ v = 0 → v = 0 := fun v hv => by
      have h := (hmem v).mpr hv
      rw [hJ] at h
      exact (Submodule.mem_bot _).mp h
    by_cases h0 : w 0 = 0
    · have h := hbot (Pi.single 0 1) (by rw [dotProduct_single, mul_one, h0])
      exact absurd (congrFun h 0) (by simp)
    · by_cases h1 : w 1 = 0
      · have h := hbot (Pi.single 1 1) (by rw [dotProduct_single, mul_one, h1])
        exact absurd (congrFun h 1) (by simp)
      · have h := hbot (Pi.single 0 1 + Pi.single 1 1) (by
          rw [dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one, key _ h0,
            key _ h1]
          rfl)
        exact absurd (congrFun h 0) (by simp)
  · funext i
    have h := (hmem (Pi.single i 1)).mp (hJ ▸ Submodule.mem_top)
    rw [dotProduct_single, mul_one] at h
    exact h

theorem m22_quad_unique_of
    (hcomm : ∀ A : Matrix (Fin 12) (Fin 12) (ZMod 2),
      A * (m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        (m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A →
      A * (m22b : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        (m22b : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A → A = 0 ∨ A = 1)
    (hirr : ∀ J : Submodule (ZMod 2) (Fin 12 → ZMod 2),
      (∀ γ ∈ m22, ∀ v ∈ J, (γ : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v ∈ J) → J = ⊥ ∨ J = ⊤)
    {Q' : (Fin 12 → ZMod 2) → ZMod 2} {B' : LinearMap.BilinForm (ZMod 2) (Fin 12 → ZMod 2)}
    (hQ' : ∀ x y, Q' (x + y) = Q' x + Q' y + B' x y) (hB' : B' ≠ 0)
    (hinv : ∀ γ ∈ m22, ∀ x, Q' ((γ : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ x) = Q' x) :
    ∀ x, Q' x = quadOf q12 x :=
  eq_quad_of_comm (S := (m22 : Set (GL (Fin 12) (ZMod 2)))) quad_m22 gram_inv
    (fun A hA => hcomm A (hA m22a (Subgroup.subset_closure (by simp)))
      (hA m22b (Subgroup.subset_closure (by simp))))
    (cov_of_irr hirr) hQ' hB' hinv

end CFSG.Quasithin.H13.M22Quad
