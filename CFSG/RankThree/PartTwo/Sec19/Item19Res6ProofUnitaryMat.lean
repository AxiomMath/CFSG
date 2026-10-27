module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryArith

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f : ℕ} {K : Type} [Field K]

section Scalars

variable {h : UnitaryFieldData p f K}

theorem scalar_mem_unitaryIsom3 {μ : Kˣ} (hμ : h.norm (μ : K) = 1) :
    GeneralLinearGroup.scalar (Fin 3) μ ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, scalar_apply,
    diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [UnitaryFieldData.norm] at hμ
  rw [mul_comm]
  exact hμ

theorem norm_eq_one_of_scalar_mem {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h) : h.norm (c : K) = 1 := by
  have h1 := congrFun (congrFun (mem_unitaryIsom3.1 hc) 0) 0
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_map (map_zero h.bar),
    diagonal_transpose, diagonal_mul_diagonal, diagonal_apply_eq, Matrix.one_apply_eq] at h1
  rw [UnitaryFieldData.norm, mul_comm]
  exact h1

theorem norm_det_eq_one {W : GL (Fin 3) K} (hW : W ∈ unitaryIsom3 h) :
    h.norm (W : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h1 := congrArg Matrix.det (mem_unitaryIsom3.1 hW)
  rw [det_mul, det_transpose, det_one, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  rw [UnitaryFieldData.norm, mul_comm]
  exact h1

end Scalars

section Eigen

theorem fin_three_cover {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (m : Fin 3) :
    m = i ∨ m = j ∨ m = l := by
  rw [Ne, Fin.ext_iff] at hij hil hjl
  rw [Fin.ext_iff, Fin.ext_iff, Fin.ext_iff]
  have := i.isLt
  have := j.isLt
  have := l.isLt
  have := m.isLt
  omega

theorem toral_joint_ne {F : Type} [Field F] {x y P : GL (Fin 3) F} {dx dy : Fin 3 → F}
    (hx : ((P * x * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal dx)
    (hy : ((P * y * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal dy)
    {α β : F} (hdx : ∀ i, dx i ^ 3 = α) (hdy : ∀ i, dy i ^ 3 = β)
    (hind : ∀ a b : ℕ, (∃ c : Fˣ, x ^ a * y ^ b = GeneralLinearGroup.scalar (Fin 3) c) →
      3 ∣ a ∧ 3 ∣ b)
    {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    dx i ≠ dx j ∨ dy i ≠ dy j := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hxij, hyij⟩ := hcon
  have hne0 : ∀ (z : GL (Fin 3) F) (d : Fin 3 → F),
      ((P * z * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal d → ∀ m, d m ≠ 0 := by
    intro z d hz m h0
    have hdet := ((P * z * P⁻¹ : GL (Fin 3) F)).isUnit.map Matrix.detMonoidHom
    apply hdet.ne_zero
    change ((P * z * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 0
    rw [hz, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ m) h0
  have hx0 := hne0 x dx hx
  have hy0 := hne0 y dy hy
  set r := dx l / dx i with hr
  set s := dy l / dy i with hs
  have hr3 : r ^ 3 = 1 := by
    rw [hr, div_pow, hdx, hdx, div_self]
    rw [← hdx i]
    exact pow_ne_zero _ (hx0 i)
  have hs3 : s ^ 3 = 1 := by
    rw [hs, div_pow, hdy, hdy, div_self]
    rw [← hdy i]
    exact pow_ne_zero _ (hy0 i)
  have hdxl : dx l = r * dx i := by rw [hr, div_mul_cancel₀ _ (hx0 i)]
  have hdyl : dy l = s * dy i := by rw [hs, div_mul_cancel₀ _ (hy0 i)]
  have key : ∀ a b : ℕ, r ^ a * s ^ b = 1 →
      ∃ c : Fˣ, x ^ a * y ^ b = GeneralLinearGroup.scalar (Fin 3) c := by
    intro a b hab
    have hc0 : dx i ^ a * dy i ^ b ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (hx0 i)) (pow_ne_zero _ (hy0 i))
    refine ⟨Units.mk0 _ hc0, ?_⟩
    have hconj : ((P * (x ^ a * y ^ b) * P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hc0) : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) := by
      have e1 : P * (x ^ a * y ^ b) * P⁻¹ = (P * x * P⁻¹) ^ a * (P * y * P⁻¹) ^ b := by
        rw [conj_pow, conj_pow]
        group
      rw [e1, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hx, hy,
        diagonal_pow, diagonal_pow, diagonal_mul_diagonal, GeneralLinearGroup.coe_scalar,
        scalar_apply]
      congr 1
      funext m
      rcases fin_three_cover hij hil hjl m with rfl | rfl | rfl
      · rfl
      · simp [hxij, hyij]
      · simp only [Pi.pow_apply, Units.val_mk0]
        rw [hdxl, hdyl, mul_pow, mul_pow]
        linear_combination (dx i ^ a * dy i ^ b) * hab
    have e2 : x ^ a * y ^ b = P⁻¹ * (P * (x ^ a * y ^ b) * P⁻¹) * P := by group
    rw [e2]
    have e3 : P * (x ^ a * y ^ b) * P⁻¹ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hc0) :=
      Units.ext hconj
    rw [e3, mul_assoc, ← (commute_scalar (Units.mk0 _ hc0) P).eq, ← mul_assoc, inv_mul_cancel,
      one_mul]
  by_cases hr1 : r = 1
  · have := hind 1 0 (key 1 0 (by rw [pow_one, pow_zero, mul_one, hr1]))
    omega
  have hrr : r ^ 2 + r + 1 = 0 := by
    have h1 : (r - 1) * (r ^ 2 + r + 1) = 0 := by linear_combination hr3
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hr1)
  have hfac : (s - 1) * (s - r) * (s - r ^ 2) = 0 := by
    linear_combination hs3 + (s - s ^ 2) * hrr + (s - 1) * hr3
  rcases mul_eq_zero.1 hfac with h12 | h3
  · rcases mul_eq_zero.1 h12 with h1 | h2
    · have hs1 : s = 1 := sub_eq_zero.1 h1
      have := hind 0 1 (key 0 1 (by rw [pow_zero, pow_one, one_mul, hs1]))
      omega
    · have hsr : s = r := sub_eq_zero.1 h2
      have := hind 1 2 (key 1 2 (by rw [hsr, pow_one, ← pow_succ']; exact hr3))
      omega
  · have hsr : s = r ^ 2 := sub_eq_zero.1 h3
    have := hind 1 1 (key 1 1 (by rw [hsr, pow_one, pow_one, ← pow_succ']; exact hr3))
    omega

variable {e : ℕ} {F : Type} [Field F]

theorem bar_mul_ne_one_of_ne (h₀ : UnitaryFieldData p e F) {a b : F} (ha : h₀.norm a = 1)
    (hab : a ≠ b) : h₀.bar a * b ≠ 1 := by
  intro h1
  apply hab
  have hN : a * h₀.bar a = 1 := ha
  calc a = a * (h₀.bar a * b) := by rw [h1, mul_one]
    _ = (a * h₀.bar a) * b := by ring
    _ = b := by rw [hN, one_mul]

theorem heis_bar_mul_ne_one (h₀ : UnitaryFieldData p e F) (hq : p ^ e % 3 = 2) {μ w : F}
    (hμ : h₀.norm μ = 1) (hw : IsPrimitiveRoot w 3) {i j : Fin 3} (hij : i ≠ j) :
    h₀.bar (![μ, μ * w, μ * w ^ 2] i) * ![μ, μ * w, μ * w ^ 2] j ≠ 1 := by
  have hw3 : w ^ 3 = 1 := hw.pow_eq_one
  have hbw : h₀.bar w = w ^ 2 := bar_eq_of_cube h₀ hq hw3
  have hd : ∀ m : Fin 3, ![μ, μ * w, μ * w ^ 2] m = μ * w ^ (m : ℕ) := by
    intro m
    fin_cases m <;> simp
  have hN : h₀.bar μ * μ = 1 := by rw [mul_comm]; exact hμ
  rw [hd, hd, map_mul, map_pow, hbw, ← pow_mul]
  have e1 : h₀.bar μ * w ^ (2 * (i : ℕ)) * (μ * w ^ (j : ℕ)) = w ^ (2 * (i : ℕ) + j) := by
    rw [pow_add]
    linear_combination (w ^ (2 * (i : ℕ)) * w ^ (j : ℕ)) * hN
  rw [e1, Ne, hw.pow_eq_one_iff_dvd]
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have := i.isLt
  have := j.isLt
  omega

end Eigen

section Twisted

theorem cyc_mul_diagonal {R : Type*} [CommRing R] (a b c x y z : R) :
    !![0, 0, a; b, 0, 0; 0, c, 0] * diagonal ![x, y, z] =
      diagonal ![z, x, y] * !![0, 0, a; b, 0, 0; 0, c, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem glAut_conj_twisted {σ : K ≃+* K} (hσσσ : ∀ x, σ (σ (σ x)) = x) {Q W : GL (Fin 3) K}
    (hQσ : glAut σ Q = Q) (hWσ : glAut σ W = W) {a b c : K}
    (hWQ : (W : Matrix (Fin 3) (Fin 3) K) * Q = Q * !![0, 0, a; b, 0, 0; 0, c, 0])
    {u : K} {D : GL (Fin 3) K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal ![u, σ u, σ (σ u)]) :
    glAut σ (W * (Q * D * Q⁻¹) * W⁻¹) = Q * D * Q⁻¹ := by
  set C : Matrix (Fin 3) (Fin 3) K := !![0, 0, a; b, 0, 0; 0, c, 0] with hC
  have hfix : ∀ A : GL (Fin 3) K, glAut σ A = A →
      (A : Matrix (Fin 3) (Fin 3) K).map σ = A := fun A hA => by
    rw [← coe_glAut, hA]
  have hQi : glAut σ Q⁻¹ = Q⁻¹ := by rw [map_inv, hQσ]
  have hWi : glAut σ W⁻¹ = W⁻¹ := by rw [map_inv, hWσ]
  have hDσ : (D : Matrix (Fin 3) (Fin 3) K).map σ = diagonal ![σ u, σ (σ u), u] := by
    rw [hD, diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i <;> simp [hσσσ]
  have hCD : C * diagonal ![σ u, σ (σ u), u] = diagonal ![u, σ u, σ (σ u)] * C := by
    rw [hC]
    exact cyc_mul_diagonal a b c (σ u) (σ (σ u)) u
  have hQQ : (Q : Matrix (Fin 3) (Fin 3) K) * ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := Units.mul_inv Q
  have hWW : (W : Matrix (Fin 3) (Fin 3) K) * ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := Units.mul_inv W
  have hQiQ : ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (Q : Matrix (Fin 3) (Fin 3) K) =
      1 := Units.inv_mul Q
  have hCQ : C * ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    calc C * ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (Q * C) *
          ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [← Matrix.mul_assoc _ (Q : Matrix (Fin 3) (Fin 3) K), hQiQ, Matrix.one_mul]
      _ = ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [← hWQ]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (Q : Matrix (Fin 3) (Fin 3) K), hQQ, Matrix.one_mul, hWW,
            Matrix.mul_one]
  apply Units.ext
  rw [coe_glAut, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hfix W hWσ, hfix Q hQσ, hfix _ hQi,
    hfix _ hWi, hDσ]
  calc (W : Matrix (Fin 3) (Fin 3) K) * ((Q : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![σ u, σ (σ u), u] * ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = (Q : Matrix (Fin 3) (Fin 3) K) * (C * diagonal ![σ u, σ (σ u), u]) *
        ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hWQ]
        simp only [Matrix.mul_assoc]
    _ = (Q : Matrix (Fin 3) (Fin 3) K) * diagonal ![u, σ u, σ (σ u)] *
        (C * ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
        rw [hCD]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hCQ, hD]

end Twisted

end CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof
