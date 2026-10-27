module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Crit
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
import CFSG.RankThree.PartTwo.Sec4.LThreePiEigen
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Iso

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open Matrix

variable {K : Type} [Field K]

private theorem entry_eq_zero_of_commute_diagonal {d : Fin 3 → K} {M : Matrix (Fin 3) (Fin 3) K}
    (h : M * diagonal d = diagonal d * M) {i j : Fin 3} (hij : d i ≠ d j) : M i j = 0 := by
  have e := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  have : M i j * (d j - d i) = 0 := by rw [mul_sub, e, mul_comm, sub_self]
  exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hij))

private theorem conj_commute_of_commute {x G g : GL (Fin 3) K} {Λ : Matrix (Fin 3) (Fin 3) K}
    (hxG : (x : Matrix (Fin 3) (Fin 3) K) * G = G * Λ) (hg : g * x = x * g) :
    ((G⁻¹ * g * G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Λ =
      Λ * ((G⁻¹ * g * G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have hGi : (G⁻¹ : GL (Fin 3) K).val * (x : Matrix (Fin 3) (Fin 3) K) =
      Λ * (G⁻¹ : GL (Fin 3) K).val := by
    calc (G⁻¹ : GL (Fin 3) K).val * (x : Matrix (Fin 3) (Fin 3) K)
        = (G⁻¹ : GL (Fin 3) K).val * (x : Matrix (Fin 3) (Fin 3) K) *
            ((G : Matrix (Fin 3) (Fin 3) K) * (G⁻¹ : GL (Fin 3) K).val) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = (G⁻¹ : GL (Fin 3) K).val * ((x : Matrix (Fin 3) (Fin 3) K) * G) *
            (G⁻¹ : GL (Fin 3) K).val := by
          simp only [Matrix.mul_assoc]
      _ = Λ * (G⁻¹ : GL (Fin 3) K).val := by
          rw [hxG]
          simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hg' : (g : Matrix (Fin 3) (Fin 3) K) * x = x * g := by
    simpa [Units.val_mul] using congrArg Units.val hg
  simp only [Units.val_mul]
  calc (G⁻¹ : GL (Fin 3) K).val * (g : Matrix (Fin 3) (Fin 3) K) * (G : Matrix (Fin 3) (Fin 3) K) *
        Λ
      = (G⁻¹ : GL (Fin 3) K).val * (g : Matrix (Fin 3) (Fin 3) K) *
          ((G : Matrix (Fin 3) (Fin 3) K) * Λ) := by simp only [Matrix.mul_assoc]
    _ = (G⁻¹ : GL (Fin 3) K).val * (g : Matrix (Fin 3) (Fin 3) K) *
          ((x : Matrix (Fin 3) (Fin 3) K) * G) := by rw [hxG]
    _ = (G⁻¹ : GL (Fin 3) K).val * ((g : Matrix (Fin 3) (Fin 3) K) * x) *
          (G : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
    _ = (G⁻¹ : GL (Fin 3) K).val * ((x : Matrix (Fin 3) (Fin 3) K) * g) *
          (G : Matrix (Fin 3) (Fin 3) K) := by rw [hg']
    _ = ((G⁻¹ : GL (Fin 3) K).val * (x : Matrix (Fin 3) (Fin 3) K)) * g *
          (G : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
    _ = Λ * ((G⁻¹ : GL (Fin 3) K).val * (g : Matrix (Fin 3) (Fin 3) K) *
          (G : Matrix (Fin 3) (Fin 3) K)) := by
          rw [hGi]
          simp only [Matrix.mul_assoc]

private theorem eq_diagonal_of_commute {d : Fin 3 → K} (hd : Function.Injective d)
    {M : Matrix (Fin 3) (Fin 3) K} (h : M * diagonal d = diagonal d * M) :
    M = diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [entry_eq_zero_of_commute_diagonal h (fun e => hij (hd e))]
    simp [Matrix.diagonal_apply_ne _ hij]

private theorem commute_of_commute_regular {x G : GL (Fin 3) K} {d : Fin 3 → K}
    (hd : Function.Injective d)
    (hxG : (x : Matrix (Fin 3) (Fin 3) K) * G = G * diagonal d)
    {g h : GL (Fin 3) K} (hg : g * x = x * g) (hh : h * x = x * h) : g * h = h * g := by
  have hg₁ := eq_diagonal_of_commute hd (conj_commute_of_commute hxG hg)
  have hh₁ := eq_diagonal_of_commute hd (conj_commute_of_commute hxG hh)
  obtain ⟨g₁, hg₁def⟩ : ∃ g₁ : GL (Fin 3) K, g₁ = G⁻¹ * g * G := ⟨_, rfl⟩
  obtain ⟨h₁, hh₁def⟩ : ∃ h₁ : GL (Fin 3) K, h₁ = G⁻¹ * h * G := ⟨_, rfl⟩
  rw [← hg₁def] at hg₁
  rw [← hh₁def] at hh₁
  have hc : g₁ * h₁ = h₁ * g₁ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hg₁, hh₁, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have e1 : g * h = G * (g₁ * h₁) * G⁻¹ := by rw [hg₁def, hh₁def]; group
  have e2 : h * g = G * (h₁ * g₁) * G⁻¹ := by rw [hg₁def, hh₁def]; group
  rw [e1, e2, hc]

private theorem injective_vec3 {p q r : K} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Function.Injective ![p, q, r] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first | exact absurd hij ‹_› | exact absurd hij.symm ‹_›

private theorem regular_or_diagE (h3 : (3 : K) ≠ 0) {τ μ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hμ : μ ≠ 0) (x : GL (Fin 3) K)
    (hx3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = μ ^ 3 • (1 : Matrix (Fin 3) (Fin 3) K))
    (hxs : ∀ s : K, (x : Matrix (Fin 3) (Fin 3) K) ≠ s • 1) :
    (∀ g h : GL (Fin 3) K, g * x = x * g → h * x = x * h → g * h = h * g) ∨
      ∃ (G : GL (Fin 3) K) (a b : K), b ≠ 0 ∧ a ≠ b ∧ a ^ 3 = b ^ 3 ∧
        (x : Matrix (Fin 3) (Fin 3) K) * G = G * diagonal ![a, b, b] := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hτ12 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * (1 - τ) = 0 := by linear_combination h
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hτ0)).symm
  set y : Matrix (Fin 3) (Fin 3) K := μ⁻¹ • (x : Matrix (Fin 3) (Fin 3) K) with hy
  have hy3 : y ^ 3 = 1 := by
    rw [hy, smul_pow, hx3, smul_smul, ← mul_pow, inv_mul_cancel₀ hμ, one_pow, one_smul]
  have hys : ∀ c : K, y ≠ c • 1 := by
    intro c hc
    apply hxs (μ * c)
    have : (x : Matrix (Fin 3) (Fin 3) K) = μ • y := by
      rw [hy, smul_smul, mul_inv_cancel₀ hμ, one_smul]
    rw [this, hc, smul_smul]
  obtain ⟨g, j, hu, h⟩ := CFSG.RankThree.PartTwo.Sec4.exists_normal_form hτ hτ1 h3 hy3 hys
  set κ : K := τ ^ (j : ℕ) * μ⁻¹ with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero (pow_ne_zero _ hτ0) (inv_ne_zero hμ)
  set G : GL (Fin 3) K := hu.unit with hG
  have hGg : (G : Matrix (Fin 3) (Fin 3) K) = g := hu.unit_spec
  have key : ∀ D : Matrix (Fin 3) (Fin 3) K, (τ ^ (j : ℕ) • y) * g = g * D →
      (x : Matrix (Fin 3) (Fin 3) K) * G = G * (κ⁻¹ • D) := by
    intro D hD
    rw [hGg, Matrix.mul_smul]
    have h1 : (τ ^ (j : ℕ) • y) = κ • (x : Matrix (Fin 3) (Fin 3) K) := by
      rw [hy, smul_smul]
    rw [h1, Matrix.smul_mul] at hD
    calc (x : Matrix (Fin 3) (Fin 3) K) * g
        = κ⁻¹ • (κ • ((x : Matrix (Fin 3) (Fin 3) K) * g)) := by
          rw [smul_smul, inv_mul_cancel₀ hκ0, one_smul]
      _ = κ⁻¹ • (g * D) := by rw [hD]
  rcases h with h | h | h
  · left
    have hxG := key _ h
    have hd : (κ⁻¹ • diagonal ![τ, τ ^ 2, 1] : Matrix (Fin 3) (Fin 3) K) =
        diagonal ![κ⁻¹ * τ, κ⁻¹ * τ ^ 2, κ⁻¹ * 1] := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      fin_cases i <;> simp
    rw [hd] at hxG
    refine fun g h hg hh => commute_of_commute_regular ?_ hxG hg hh
    refine injective_vec3 ?_ ?_ ?_
    · intro e
      exact hτ12 (mul_left_cancel₀ (inv_ne_zero hκ0) e)
    · intro e
      exact hτ1 (by simpa [inv_ne_zero hκ0] using e)
    · intro e
      exact hτ2 (by simpa [inv_ne_zero hκ0] using e)
  · right
    have hxG := key _ h
    have hd : (κ⁻¹ • diagonal ![τ, 1, 1] : Matrix (Fin 3) (Fin 3) K) =
        diagonal ![κ⁻¹ * τ, κ⁻¹, κ⁻¹] := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      fin_cases i <;> simp
    rw [hd] at hxG
    refine ⟨G, κ⁻¹ * τ, κ⁻¹, inv_ne_zero hκ0, ?_, ?_, hxG⟩
    · intro e
      exact hτ1 (by simpa [inv_ne_zero hκ0] using e)
    · rw [mul_pow, hτ, mul_one]
  · right
    have hxG := key _ h
    have hd : (κ⁻¹ • diagonal ![τ ^ 2, 1, 1] : Matrix (Fin 3) (Fin 3) K) =
        diagonal ![κ⁻¹ * τ ^ 2, κ⁻¹, κ⁻¹] := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext i
      fin_cases i <;> simp
    rw [hd] at hxG
    refine ⟨G, κ⁻¹ * τ ^ 2, κ⁻¹, inv_ne_zero hκ0, ?_, ?_, hxG⟩
    · intro e
      exact hτ2 (by simpa [inv_ne_zero hκ0] using e)
    · rw [mul_pow, ← pow_mul, mul_comm 2 3, pow_mul, hτ, one_pow, mul_one]

private theorem coe_scalar_eq (u : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (u : K) • 1 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

private theorem scalar_comm (w : Kˣ) (a : GL (Fin 3) K) :
    a * GeneralLinearGroup.scalar (Fin 3) w = GeneralLinearGroup.scalar (Fin 3) w * a := by
  have : GeneralLinearGroup.scalar (Fin 3) w ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨w, rfl⟩
  exact Subgroup.mem_center_iff.mp this a

private theorem commutator_commute_matrix {n : Type} [Fintype n] [DecidableEq n]
    {A Ai B Bi X : Matrix n n K} {u v : K} (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A * Ai = 1) (hAi : Ai * A = 1) (hB : B * Bi = 1) (hBi : Bi * B = 1)
    (hg : A * X = u • (X * A)) (hh : B * X = v • (X * B)) :
    (A * B * Ai * Bi) * X = X * (A * B * Ai * Bi) := by
  have hgi : Ai * X = u⁻¹ • (X * Ai) := by
    calc Ai * X = Ai * (X * A) * Ai := by
          simp only [Matrix.mul_assoc, hA, Matrix.mul_one]
      _ = Ai * (u⁻¹ • (A * X)) * Ai := by
          congr 2
          rw [hg, smul_smul, inv_mul_cancel₀ hu, one_smul]
      _ = u⁻¹ • (X * Ai) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hAi, Matrix.one_mul]
  have hhi : Bi * X = v⁻¹ • (X * Bi) := by
    calc Bi * X = Bi * (X * B) * Bi := by
          simp only [Matrix.mul_assoc, hB, Matrix.mul_one]
      _ = Bi * (v⁻¹ • (B * X)) * Bi := by
          congr 2
          rw [hh, smul_smul, inv_mul_cancel₀ hv, one_smul]
      _ = v⁻¹ • (X * Bi) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hBi, Matrix.one_mul]
  calc (A * B * Ai * Bi) * X = A * B * Ai * (Bi * X) := by simp only [Matrix.mul_assoc]
    _ = v⁻¹ • (A * B * (Ai * X) * Bi) := by
        rw [hhi]
        simp only [Matrix.mul_smul, Matrix.mul_assoc]
    _ = (v⁻¹ * u⁻¹) • (A * (B * X) * Ai * Bi) := by
        rw [hgi]
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
    _ = (v⁻¹ * u⁻¹ * v) • (A * X * B * Ai * Bi) := by
        rw [hh]
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
    _ = (v⁻¹ * u⁻¹ * v * u) • (X * A * B * Ai * Bi) := by
        rw [hg]
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
    _ = X * (A * B * Ai * Bi) := by
        have : v⁻¹ * u⁻¹ * v * u = 1 := by field_simp
        rw [this, one_smul]
        simp only [Matrix.mul_assoc]

private theorem twist_matrix {x g : GL (Fin 3) K} {u : Kˣ}
    (hg : g * x * g⁻¹ = x * GeneralLinearGroup.scalar (Fin 3) u) :
    (g : Matrix (Fin 3) (Fin 3) K) * x = (u : K) • ((x : Matrix (Fin 3) (Fin 3) K) * g) := by
  have h1 : g * x = x * GeneralLinearGroup.scalar (Fin 3) u * g := by
    calc g * x = g * x * g⁻¹ * g := by group
      _ = _ := by rw [hg]
  have h2 := congrArg Units.val h1
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scalar_eq, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul] at h2
  exact h2

private theorem commutator_commute {x g h : GL (Fin 3) K} {u v : Kˣ}
    (hg : g * x * g⁻¹ = x * GeneralLinearGroup.scalar (Fin 3) u)
    (hh : h * x * h⁻¹ = x * GeneralLinearGroup.scalar (Fin 3) v) :
    g * h * g⁻¹ * h⁻¹ * x = x * (g * h * g⁻¹ * h⁻¹) := by
  apply Units.ext
  simp only [Units.val_mul]
  exact commutator_commute_matrix u.ne_zero v.ne_zero (Units.mul_inv g) (Units.inv_mul g)
    (Units.mul_inv h) (Units.inv_mul h) (twist_matrix hg) (twist_matrix hh)

private theorem coe_eq_of_mul_eq {x G : GL (Fin 3) K} {Λ : Matrix (Fin 3) (Fin 3) K}
    (hxG : (x : Matrix (Fin 3) (Fin 3) K) * G = G * Λ) :
    (x : Matrix (Fin 3) (Fin 3) K) = G * Λ * (G⁻¹ : GL (Fin 3) K) := by
  rw [← hxG, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

private theorem twist_eq_one_of_diagE (h3 : (3 : K) ≠ 0) {x G : GL (Fin 3) K} {a b : K}
    (hb : b ≠ 0) (ha3 : a ^ 3 = b ^ 3)
    (hxG : (x : Matrix (Fin 3) (Fin 3) K) * G = G * diagonal ![a, b, b])
    {g : GL (Fin 3) K} {u : Kˣ}
    (hg : g * x * g⁻¹ = x * GeneralLinearGroup.scalar (Fin 3) u) : g * x = x * g := by
  have htr : (x : Matrix (Fin 3) (Fin 3) K).trace = a + b + b := by
    rw [coe_eq_of_mul_eq hxG, Matrix.trace_units_conj, Matrix.trace_diagonal, Fin.sum_univ_three]
    simp
  have hne : a + b + b ≠ 0 := by
    intro h0
    have h9 : (9 : K) * b ^ 3 = 0 := by
      linear_combination (a ^ 2 - 2 * a * b + 4 * b ^ 2) * h0 - ha3
    have h9' : (9 : K) = 0 := (mul_eq_zero.mp h9).resolve_right (pow_ne_zero 3 hb)
    apply h3
    have : (3 : K) * 3 = 0 := by rw [← h9']; norm_num
    exact mul_self_eq_zero.mp this
  have htr2 := congrArg (fun m : GL (Fin 3) K => (m : Matrix (Fin 3) (Fin 3) K).trace) hg
  simp only [Units.val_mul, coe_scalar_eq, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    Matrix.trace_units_conj, smul_eq_mul] at htr2
  have hu : (u : K) = 1 := by
    have h0 : ((u : K) - 1) * (a + b + b) = 0 := by
      rw [← htr]
      linear_combination -htr2
    have := (mul_eq_zero.mp h0).resolve_right hne
    exact sub_eq_zero.mp this
  have hu1 : u = 1 := Units.ext hu
  rw [hu1, map_one, mul_one] at hg
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [hg]

section Psi

variable {x G : GL (Fin 3) K}

private noncomputable def d1 (G g : GL (Fin 3) K) : K :=
  ((G⁻¹ * g * G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0

private theorem d1_one (G : GL (Fin 3) K) : d1 G 1 = 1 := by
  simp [d1]

private theorem d1_mul {G g h : GL (Fin 3) K}
    (h01 : ((G⁻¹ * g * G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (h02 : ((G⁻¹ * g * G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0) :
    d1 G (g * h) = d1 G g * d1 G h := by
  have e : G⁻¹ * (g * h) * G = (G⁻¹ * g * G) * (G⁻¹ * h * G) := by group
  unfold d1
  rw [e, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h01, h02]
  simp

private theorem d1_scalar (G : GL (Fin 3) K) (u : Kˣ) :
    d1 G (GeneralLinearGroup.scalar (Fin 3) u) = u := by
  have e : G⁻¹ * GeneralLinearGroup.scalar (Fin 3) u * G =
      GeneralLinearGroup.scalar (Fin 3) u := by
    rw [mul_assoc, ← scalar_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  unfold d1
  rw [e, coe_scalar_eq]
  simp

private theorem conj_entry_zero {a b : K} (hab : a ≠ b)
    (hxG : (x : Matrix (Fin 3) (Fin 3) K) * G = G * diagonal ![a, b, b])
    {g : GL (Fin 3) K} (hg : g * x = x * g) :
    ((G⁻¹ * g * G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧
      ((G⁻¹ * g * G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
  have h := conj_commute_of_commute hxG hg
  exact ⟨entry_eq_zero_of_commute_diagonal h (by simpa using hab),
    entry_eq_zero_of_commute_diagonal h (by simpa using hab)⟩

private noncomputable def dHom0 {a b : K} (hab : a ≠ b)
    (hxG : (x : Matrix (Fin 3) (Fin 3) K) * G = G * diagonal ![a, b, b]) :
    Subgroup.centralizer ({x} : Set (GL (Fin 3) K)) →* K where
  toFun g := d1 G (g : GL (Fin 3) K)
  map_one' := d1_one G
  map_mul' g h := by
    have hg : (g : GL (Fin 3) K) * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp g.2
    obtain ⟨h01, h02⟩ := conj_entry_zero hab hxG hg
    exact d1_mul h01 h02

private theorem exists_psi {a b : K} (hb : b ≠ 0) (hab : a ≠ b) (ha3 : a ^ 3 = b ^ 3)
    (hxG : (x : Matrix (Fin 3) (Fin 3) K) * G = G * diagonal ![a, b, b]) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (GL (Fin 3) K)) →* Kˣ,
      (∀ (u : Kˣ) (g : Subgroup.centralizer ({x} : Set (GL (Fin 3) K))),
          (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) u → ψ g = 1) ∧
      (∀ g : Subgroup.centralizer ({x} : Set (GL (Fin 3) K)),
          (g : GL (Fin 3) K) = x → ψ g ≠ 1) := by
  set dH : Subgroup.centralizer ({x} : Set (GL (Fin 3) K)) →* Kˣ :=
    (dHom0 hab hxG).toHomUnits with hdH
  have hdH_val : ∀ g : Subgroup.centralizer ({x} : Set (GL (Fin 3) K)),
      (dH g : K) = d1 G (g : GL (Fin 3) K) := fun g => rfl
  refine ⟨GeneralLinearGroup.det.comp (Subgroup.centralizer ({x} : Set (GL (Fin 3) K))).subtype *
    (dH⁻¹) ^ 3, ?_, ?_⟩
  · intro u g hg
    have hdet : GeneralLinearGroup.det (g : GL (Fin 3) K) = u ^ 3 := by
      rw [hg, GeneralLinearGroup.det_scalar, Fintype.card_fin]
    have hd : dH g = u := by
      apply Units.ext
      rw [hdH_val, hg, d1_scalar]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply,
      MonoidHom.comp_apply, Subgroup.subtype_apply]
    rw [hdet, hd, ← mul_pow, mul_inv_cancel, one_pow]
  · intro g hg hψ
    have hdet : ((GeneralLinearGroup.det x : Kˣ) : K) = a * b * b := by
      rw [GeneralLinearGroup.val_det_apply, coe_eq_of_mul_eq hxG, Matrix.det_units_conj,
        det_diagonal, Fin.prod_univ_three]
      simp
    have hd : (dH g : K) = a := by
      rw [hdH_val, d1, hg]
      have : ((G⁻¹ * x * G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          diagonal ![a, b, b] := by
        rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hxG, ← Matrix.mul_assoc,
          Units.inv_mul, Matrix.one_mul]
      rw [this]
      simp
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply,
      MonoidHom.comp_apply, Subgroup.subtype_apply] at hψ
    have h1 := congrArg Units.val hψ
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hg, hdet, hd,
      Units.val_one] at h1
    have ha0 : a ≠ 0 := by
      intro h0
      apply hb
      have : b ^ 3 = 0 := by rw [← ha3, h0]; norm_num
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    field_simp at h1
    apply hab
    have h2 : a ^ 2 * (a - b) = 0 := by
      linear_combination ha3 + b * h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) ha0
    · exact sub_eq_zero.mp h

end Psi

private theorem exists_twist {S : Subgroup (ProjGenLinGroup (Fin 3) K)} {c : S}
    {x : GL (Fin 3) K} (hx : ProjGenLinGroup.mk x = (c : ProjGenLinGroup (Fin 3) K))
    {g : S} (hg : g ∈ Subgroup.centralizer ({c} : Set S)) :
    ∃ g' : GL (Fin 3) K, ProjGenLinGroup.mk g' = (g : ProjGenLinGroup (Fin 3) K) ∧
      ∃ u : Kˣ, g' * x * g'⁻¹ = x * GeneralLinearGroup.scalar (Fin 3) u := by
  obtain ⟨g', hg'⟩ := ProjGenLinGroup.mk_surjective (g : ProjGenLinGroup (Fin 3) K)
  refine ⟨g', hg', ?_⟩
  have hgc : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have h1 : ProjGenLinGroup.mk (g' * x) = ProjGenLinGroup.mk (x * g') := by
    rw [map_mul, map_mul, hg', hx]
    exact congrArg Subtype.val hgc
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h1
  refine ⟨u⁻¹, ?_⟩
  have h2 : g' * x = x * g' * GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
    calc g' * x = g' * x * GeneralLinearGroup.scalar (Fin 3) u *
          GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
          rw [mul_assoc (g' * x), ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = _ := by rw [hu]
  calc g' * x * g'⁻¹ = x * g' * GeneralLinearGroup.scalar (Fin 3) u⁻¹ * g'⁻¹ := by rw [h2]
    _ = x * (g' * GeneralLinearGroup.scalar (Fin 3) u⁻¹) * g'⁻¹ := by rw [mul_assoc x]
    _ = x * (GeneralLinearGroup.scalar (Fin 3) u⁻¹ * g') * g'⁻¹ := by rw [scalar_comm]
    _ = x * GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by group

private theorem false_of_datum {S : Subgroup (ProjGenLinGroup (Fin 3) K)} [Finite S] {c : S}
    {L : Subgroup S} (hLD : LocalDatum S c L) {x : GL (Fin 3) K}
    (hx : ProjGenLinGroup.mk x = (c : ProjGenLinGroup (Fin 3) K))
    {H₀ : Subgroup (ProjGenLinGroup (Fin 3) K)}
    (hcomm : ∀ g h : GL (Fin 3) K,
      (∃ u : Kˣ, g * x * g⁻¹ = x * GeneralLinearGroup.scalar (Fin 3) u) →
      (∃ v : Kˣ, h * x * h⁻¹ = x * GeneralLinearGroup.scalar (Fin 3) v) →
      ProjGenLinGroup.mk (g * h * g⁻¹ * h⁻¹) ∈ H₀)
    (hH₀ : (∀ p ∈ H₀, ∀ q ∈ H₀, p * q = q * p) ∨ ProjGenLinGroup.mk x ∉ H₀) : False := by
  have hLH : L ≤ H₀.comap S.subtype := by
    refine hLD.le_of_commutator_le fun y hy z hz => ?_
    obtain ⟨y', hy1, hy2⟩ := exists_twist hx hy
    obtain ⟨z', hz1, hz2⟩ := exists_twist hx hz
    show ((y * z * y⁻¹ * z⁻¹ : S) : ProjGenLinGroup (Fin 3) K) ∈ H₀
    have e : ((y * z * y⁻¹ * z⁻¹ : S) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (y' * z' * y'⁻¹ * z'⁻¹) := by
      simp only [map_mul, map_inv, hy1, hz1]
      rfl
    rw [e]
    exact hcomm _ _ hy2 hz2
  rcases hH₀ with hc | hn
  · haveI := hLD.perfect
    have hL : L ≤ ⊥ := by
      calc L = ⁅L, L⁆ := (Subgroup.commutator_eq_self (H := L)).symm
        _ ≤ ⊥ := by
          rw [Subgroup.commutator_le]
          intro a ha b hb
          rw [Subgroup.mem_bot]
          exact commutatorElement_eq_one_iff_mul_comm.mpr
            (Subtype.ext (hc _ (hLH ha) _ (hLH hb)))
    have h1 : c = 1 := Subgroup.mem_bot.mp (hL hLD.mem)
    have := hLD.orderOf_eq
    rw [h1, orderOf_one] at this
    omega
  · exact hn (hx ▸ hLH hLD.mem)

private theorem noLocalDatum_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K]
    (h3 : (3 : K) ≠ 0) (S : Subgroup (ProjGenLinGroup (Fin 3) K)) [Finite S] :
    NoLocalDatum S := by
  intro c L hLD
  obtain ⟨x, hx⟩ := ProjGenLinGroup.mk_surjective (c : ProjGenLinGroup (Fin 3) K)
  have hc3 : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hLD.orderOf_eq] at this
  have hx3 : x ^ 3 ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← ProjGenLinGroup.mk_eq_one, map_pow, hx]
    have := congrArg Subtype.val hc3
    simpa using this
  rw [GeneralLinearGroup.center_eq_range_scalar] at hx3
  obtain ⟨l, hl⟩ := hx3
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (l : K) (by norm_num : 0 < 3)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact l.ne_zero (by rw [← hμ]; norm_num)
  have hx3' : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = μ ^ 3 • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg Units.val hl
    rw [coe_scalar_eq, Units.val_pow_eq_pow_val] at this
    rw [← this, hμ]
  have hxs : ∀ s : K, (x : Matrix (Fin 3) (Fin 3) K) ≠ s • 1 := by
    intro s hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact Units.ne_zero x (by simpa using hs)
    have hxsc : x = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 s hs0) := by
      apply Units.ext
      rw [hs, coe_scalar_eq]
      rfl
    have hc1 : c = 1 := by
      apply Subtype.ext
      rw [← hx, hxsc, ProjGenLinGroup.mk_scalar]
      rfl
    have := hLD.orderOf_eq
    rw [hc1, orderOf_one] at this
    omega
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K).degree = 2 := by
    compute_degree!
  obtain ⟨τ, hτ0⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K) (by rw [hdeg]; norm_num)
  have hτ2 : τ ^ 2 + τ + 1 = 0 := by simpa using hτ0
  have hτ : τ ^ 3 = 1 := by linear_combination (τ - 1) * hτ2
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hτ2
  rcases regular_or_diagE h3 hτ hτ1 hμ0 x hx3' hxs with hreg | ⟨G, a, b, hb, hab, ha3, hxG⟩
  · refine false_of_datum hLD hx
      (H₀ := (Subgroup.centralizer ({x} : Set (GL (Fin 3) K))).map ProjGenLinGroup.mk) ?_
      (Or.inl ?_)
    · rintro g h ⟨u, hu⟩ ⟨v, hv⟩
      exact Subgroup.mem_map_of_mem _
        (Subgroup.mem_centralizer_singleton_iff.mpr (commutator_commute hu hv))
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
      rw [← map_mul, ← map_mul, hreg g h (Subgroup.mem_centralizer_singleton_iff.mp hg)
        (Subgroup.mem_centralizer_singleton_iff.mp hh)]
  · obtain ⟨ψ, hψ1, hψ2⟩ := exists_psi hb hab ha3 hxG
    refine false_of_datum hLD hx
      (H₀ := ((ψ.ker).map (Subgroup.centralizer ({x} : Set (GL (Fin 3) K))).subtype).map
        ProjGenLinGroup.mk) ?_ (Or.inr ?_)
    · rintro g h ⟨u, hu⟩ ⟨v, hv⟩
      have hgx := twist_eq_one_of_diagE h3 hb ha3 hxG hu
      have hhx := twist_eq_one_of_diagE h3 hb ha3 hxG hv
      let gC : Subgroup.centralizer ({x} : Set (GL (Fin 3) K)) :=
        ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hgx⟩
      let hC : Subgroup.centralizer ({x} : Set (GL (Fin 3) K)) :=
        ⟨h, Subgroup.mem_centralizer_singleton_iff.mpr hhx⟩
      refine Subgroup.mem_map_of_mem _ (Subgroup.mem_map.mpr ⟨gC * hC * gC⁻¹ * hC⁻¹, ?_, rfl⟩)
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    · rintro ⟨y, hy, hkx⟩
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨w, hw⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hkx
      have hxmem : x ∈ Subgroup.centralizer ({x} : Set (GL (Fin 3) K)) :=
        Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have hwmem : GeneralLinearGroup.scalar (Fin 3) w ∈
          Subgroup.centralizer ({x} : Set (GL (Fin 3) K)) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (scalar_comm w x).symm
      have heq : (⟨x, hxmem⟩ : Subgroup.centralizer ({x} : Set (GL (Fin 3) K))) =
          k * ⟨GeneralLinearGroup.scalar (Fin 3) w, hwmem⟩ := Subtype.ext hw.symm
      refine hψ2 ⟨x, hxmem⟩ rfl ?_
      rw [heq, map_mul, MonoidHom.mem_ker.mp hk, hψ1 w ⟨_, hwmem⟩ rfl, one_mul]

private theorem projMap_injective {K K' : Type} [Field K] [Field K'] (f : K →+* K') :
    Function.Injective (ProjGenLinGroup.map (n := Fin 3) f) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  induction p using ProjGenLinGroup.induction_on with | mk g => ?_
  rw [ProjGenLinGroup.map_mk, ProjGenLinGroup.mk_eq_one, Subgroup.mem_center_iff] at hp
  rw [ProjGenLinGroup.mk_eq_one, Subgroup.mem_center_iff]
  intro h
  have hmap : Function.Injective (GeneralLinearGroup.map (n := Fin 3) f) := by
    intro a b hab
    apply Units.ext
    ext i j
    have := congrArg (fun m : GL (Fin 3) K' => (m : Matrix (Fin 3) (Fin 3) K') i j) hab
    simp only [GeneralLinearGroup.map_apply] at this
    exact f.injective this
  apply hmap
  rw [map_mul, map_mul]
  exact hp _

theorem noLocalDatum_of_le_projGL {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    (S : Subgroup (ProjGenLinGroup (Fin 3) K)) [Finite S] : NoLocalDatum S := by
  have hι := projMap_injective (algebraMap K (AlgebraicClosure K))
  have h3' : (3 : AlgebraicClosure K) ≠ 0 := by
    intro h
    apply h3
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [map_ofNat, map_zero]
    exact h
  let e := S.equivMapOfInjective _ hι
  haveI : Finite (S.map (ProjGenLinGroup.map (n := Fin 3) (algebraMap K (AlgebraicClosure K)))) :=
    Finite.of_equiv S e.toEquiv
  exact NoLocalDatum.of_mulEquiv e (noLocalDatum_of_isAlgClosed h3' _)

private theorem three_ne_zero_of_ringChar {F : Type} [Field F] (h : ringChar F ≠ 3) :
    (3 : F) ≠ 0 := by
  intro h0
  have hd : ringChar F ∣ 3 := (ringChar.spec F 3).mp (by exact_mod_cast h0)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h h3

private theorem three_ne_zero_galoisField (p n : ℕ) [Fact p.Prime] (hp : p ≠ 3) :
    (3 : GaloisField p n) ≠ 0 := by
  intro h
  have : p ∣ 3 := (CharP.cast_eq_zero_iff (GaloisField p n) p 3).mp (by exact_mod_cast h)
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp this)

theorem noLocalDatum_projSL_three (F : Type) [Field F] [Finite F] (h3 : ringChar F ≠ 3) :
    NoLocalDatum (CFSG.Assembly.RankThreeEven.projSL 3 F) :=
  noLocalDatum_of_le_projGL (three_ne_zero_of_ringChar h3) _

theorem noLocalDatum_projSU_three (p f : ℕ) [Fact p.Prime] (hp : p ≠ 3) (hf : 1 ≤ f) :
    NoLocalDatum (CFSG.Assembly.RankThreeEven.projSU 3 p f) :=
  noLocalDatum_of_le_projGL (three_ne_zero_galoisField p (2 * f) hp) _

end CFSG.RankThree.PartTwo.Sec19.SimsC198
