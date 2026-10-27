module

public import CFSG.GH74.GLS.Stage4.T2F1LocH90
public import CFSG.RankThree.PartTwo.KFacts.K71PSU3

public section

section FusH90


namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusH90

private theorem pow_succ_apply' {F : Type} [Field F] (σ : F ≃+* F) (n : ℕ) (z : F) :
    (σ ^ (n + 1)) z = σ ((σ ^ n) z) := by
  rw [pow_succ', RingAut.mul_apply]

theorem exists_hilbert90_cube {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hσ : orderOf σ = 3)
    {ω : K} (hω : ω ^ 3 = 1) (hσω : σ ω = ω) : ∃ β : K, β ≠ 0 ∧ β = ω * σ β := by
  have hpow : ∀ i : ℕ, (σ ^ i) ω = ω := by
    intro i
    induction i with
    | zero => rw [pow_zero, RingAut.one_apply]
    | succ n ih => rw [pow_succ_apply', ih, hσω]
  have hprod : ∏ i ∈ Finset.range 3, (σ ^ i) ω = 1 := by
    simp only [hpow, Finset.prod_const, Finset.card_range]
    exact hω
  obtain ⟨y, hy0, hy⟩ := CFSG.GH74.GLS.Stage4.Rest.F1Loc.hilbert90_finiteField σ hσ hprod
  exact ⟨y, hy0, hy.symm⟩

theorem apply_eq_of_cube_root {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : σ ^ 3 = 1)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : σ ω = ω := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hs : σ ω ^ 2 + σ ω + 1 = 0 := by
    have h := congrArg (fun x => σ x) hω
    simpa [map_add, map_pow, map_one, map_zero] using h
  have hprod : (σ ω - ω) * (σ ω - (ω + 1)) = 0 := by
    linear_combination hs + hω - (ω * σ ω + σ ω + 1) * h2
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hs' : σ ω = ω + 1 := sub_eq_zero.mp h
    have hss : σ (σ ω) = ω := by
      rw [hs', map_add, map_one, hs']
      linear_combination h2
    have h3 : σ (σ (σ ω)) = ω := by
      have h : (σ ^ 3) ω = ω := by rw [hσ, RingAut.one_apply]
      rw [pow_three, RingAut.mul_apply, RingAut.mul_apply] at h
      exact h
    rw [hss, hs'] at h3
    have h1 : (1 : K) = 0 := by linear_combination h3
    exact one_ne_zero h1

theorem orderOf_eq_three_of_frobenius_forms {π : Bool} {p f f₀ : ℕ} {K : Type} [Field K]
    (hK : CFSG.RankThree.PartTwo.Sec4.PiField π p f K) (hf : f = 3 * f₀) (σ : K ≃+* K)
    (hσ : (∀ c, σ c = c ^ CFSG.RankThree.PartTwo.Sec4.piCard π (p ^ f₀)) ∨
      ∀ c, σ c = c ^ (CFSG.RankThree.PartTwo.Sec4.piCard π (p ^ f₀) ^ 2)) :
    orderOf σ = 3 := by
  obtain ⟨φ, hφ, hφ3⟩ := CFSG.RankThree.PartTwo.Sec4.exists_frob hK hf
  have hcop : (orderOf φ).Coprime 2 := by
    rw [hφ3]
    norm_num
  rcases hσ with h | h
  · have hσφ : σ = φ := RingEquiv.ext fun c => (h c).trans (hφ c).symm
    rw [hσφ]
    exact hφ3
  · have hsq : ∀ c : K, (φ ^ 2) c = φ (φ c) := fun c => by
      rw [sq, RingAut.mul_apply]
    have hσφ : σ = φ ^ 2 := RingEquiv.ext fun c => by
      rw [hsq, h c, hφ c, map_pow, hφ c, ← pow_mul, sq]
    rw [hσφ]
    exact (Nat.Coprime.orderOf_pow hcop).trans hφ3

theorem exists_hilbert90_normOne {K : Type} [Field K] [Finite K] {q₀ : ℕ} (hK : Nat.card K = (q₀ ^ 3) ^ 2)
    (σ : K ≃+* K) (hσ : (∀ c, σ c = c ^ (q₀ ^ 2)) ∨ ∀ c, σ c = c ^ (q₀ ^ 4))
    {ω : Kˣ} (hω : ω ^ (q₀ ^ 3 + 1) = 1) (hω3 : ω ^ 3 = 1) :
    ∃ β : Kˣ, β ^ (q₀ ^ 3 + 1) = 1 ∧ (β : K) = (ω : K) * σ (β : K) := by
  have hF : ∀ x : K, x ^ (q₀ ^ 6) = x := by
    intro x
    letI : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = q₀ ^ 6 := by
      rw [← Nat.card_eq_fintype_card, hK]
      ring
    rw [← hcard]
    exact FiniteField.pow_card x
  have key : ∀ x : K, σ x = x → x ^ (q₀ ^ 2) = x := by
    intro x hx
    rcases hσ with h | h
    · exact (h x).symm.trans hx
    · have hx4 : x ^ (q₀ ^ 4) = x := (h x).symm.trans hx
      calc x ^ (q₀ ^ 2) = (x ^ (q₀ ^ 4)) ^ (q₀ ^ 2) := by rw [hx4]
        _ = x ^ (q₀ ^ 6) := by rw [← pow_mul, show q₀ ^ 4 * q₀ ^ 2 = q₀ ^ 6 by ring]
        _ = x := hF x
  have hfix : ∀ c : Kˣ, c ^ (q₀ ^ 3 + 1) = 1 → σ c = c → c ^ (q₀ + 1) = 1 := by
    intro c hc hσc
    have hc' : (c : K) ^ (q₀ ^ 3 + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    have hx2 : (c : K) ^ (q₀ ^ 2) = (c : K) := key _ hσc
    have h3 : (c : K) ^ (q₀ ^ 3) = (c : K) ^ q₀ := by
      rw [show q₀ ^ 3 = q₀ ^ 2 * q₀ by ring, pow_mul, hx2]
    have e1 : (c : K) ^ (q₀ ^ 3 + 1) = (c : K) ^ q₀ * (c : K) := by
      rw [pow_succ (c : K) (q₀ ^ 3), h3]
    have e2 : (c : K) ^ (q₀ + 1) = (c : K) ^ q₀ * (c : K) := pow_succ _ _
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, e2, ← e1]
    exact hc'
  obtain ⟨μ, hμ, hμσ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_normOne_field_mul_eq hK σ hfix hω hω3
  refine ⟨μ⁻¹, ?_, ?_⟩
  · rw [inv_pow, hμ, inv_one]
  · have hμ' : Units.map (σ : K →* K) μ⁻¹ = ω⁻¹ * μ⁻¹ := by
      rw [map_inv, hμσ, mul_inv]
    have key2 : ω * Units.map (σ : K →* K) μ⁻¹ = μ⁻¹ := by
      rw [hμ', mul_inv_cancel_left]
    have key3 := congrArg Units.val key2
    rw [Units.val_mul, Units.coe_map] at key3
    exact key3.symm

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusH90

end FusH90

section FusDiag


namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusDiag

open Matrix

theorem entry_eq_of_diag {K : Type} [Field K] {M : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K}
    {c : K} (H : M * Matrix.diagonal d = c • (Matrix.diagonal d * M)) (i j : Fin 3) :
    M i j * (d j - c * d i) = 0 := by
  have H' := congrArg (fun N : Matrix (Fin 3) (Fin 3) K => N i j) H
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at H'
  linear_combination H'

theorem row_ne_zero3 {K : Type} [Field K] {M : Matrix (Fin 3) (Fin 3) K} (hM : IsUnit M)
    (i : Fin 3) : M i 0 ≠ 0 ∨ M i 1 ≠ 0 ∨ M i 2 ≠ 0 := by
  by_contra hcon
  have h0 : M i 0 = 0 := by
    by_contra hne
    exact hcon (Or.inl hne)
  have h1 : M i 1 = 0 := by
    by_contra hne
    exact hcon (Or.inr (Or.inl hne))
  have h2 : M i 2 = 0 := by
    by_contra hne
    exact hcon (Or.inr (Or.inr hne))
  have hrow : ∀ j : Fin 3, M i j = 0 := by
    intro j
    fin_cases j
    exacts [h0, h1, h2]
  have hdet : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero i hrow
  exact ((Matrix.isUnit_iff_isUnit_det (A := M)).mp hM).ne_zero hdet

theorem offdiag_eq_zero_of_conj_std {K : Type} [Field K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hω1 : ω ≠ 1) {h : Matrix (Fin 3) (Fin 3) K} (hh : IsUnit h) {c₁ c₂ : K}
    (h₁ : h * Matrix.diagonal ![1, ω, ω ^ 2] = c₁ • (Matrix.diagonal ![1, ω, ω ^ 2] * h))
    (h₂ : h * Matrix.diagonal ![1, 1, ω] = c₂ • (Matrix.diagonal ![1, 1, ω] * h)) :
    ∀ i j : Fin 3, i ≠ j → h i j = 0 := by
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω
    norm_num at hω
  have hω21 : ω ^ 2 ≠ 1 := by
    intro h21
    have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
    exact hω1 (by linear_combination (-ω) * h21 + h3)
  have hω1' : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
  have hω1'' : 1 - ω ≠ 0 := fun e => hω1' (by linear_combination -e)
  have A00 : h 0 0 * (1 - c₂ * 1) = 0 := entry_eq_of_diag h₂ 0 0
  have A01 : h 0 1 * (1 - c₂ * 1) = 0 := entry_eq_of_diag h₂ 0 1
  have A02 : h 0 2 * (ω - c₂ * 1) = 0 := entry_eq_of_diag h₂ 0 2
  have A12 : h 1 2 * (ω - c₂ * 1) = 0 := entry_eq_of_diag h₂ 1 2
  have A20 : h 2 0 * (1 - c₂ * ω) = 0 := entry_eq_of_diag h₂ 2 0
  have A21 : h 2 1 * (1 - c₂ * ω) = 0 := entry_eq_of_diag h₂ 2 1
  have A22 : h 2 2 * (ω - c₂ * ω) = 0 := entry_eq_of_diag h₂ 2 2
  have hc2 : c₂ = 1 ∨ c₂ = ω := by
    rcases row_ne_zero3 hh 0 with h0 | h0 | h0
    · have e : 1 - c₂ * 1 = 0 := (mul_eq_zero.mp A00).resolve_left h0
      exact Or.inl (by linear_combination -e)
    · have e : 1 - c₂ * 1 = 0 := (mul_eq_zero.mp A01).resolve_left h0
      exact Or.inl (by linear_combination -e)
    · have e : ω - c₂ * 1 = 0 := (mul_eq_zero.mp A02).resolve_left h0
      exact Or.inr (by linear_combination -e)
  have hc2' : c₂ = 1 := by
    rcases hc2 with hc | hc
    · exact hc
    · exfalso
      rw [hc] at A20 A21 A22
      have hne1 : 1 - ω * ω ≠ 0 := fun e => hω21 (by linear_combination -e)
      have hne2 : ω - ω * ω ≠ 0 := by
        intro e
        have hm : ω * (1 - ω) = 0 := by linear_combination e
        exact hω1'' ((mul_eq_zero.mp hm).resolve_left hω0)
      rcases row_ne_zero3 hh 2 with h0 | h0 | h0
      · exact h0 ((mul_eq_zero.mp A20).resolve_right hne1)
      · exact h0 ((mul_eq_zero.mp A21).resolve_right hne1)
      · exact h0 ((mul_eq_zero.mp A22).resolve_right hne2)
  have e02 : h 0 2 * (ω - 1) = 0 := by linear_combination A02 + h 0 2 * hc2'
  have e12 : h 1 2 * (ω - 1) = 0 := by linear_combination A12 + h 1 2 * hc2'
  have e20 : h 2 0 * (1 - ω) = 0 := by linear_combination A20 + h 2 0 * ω * hc2'
  have e21 : h 2 1 * (1 - ω) = 0 := by linear_combination A21 + h 2 1 * ω * hc2'
  have z02 : h 0 2 = 0 := (mul_eq_zero.mp e02).resolve_right hω1'
  have z12 : h 1 2 = 0 := (mul_eq_zero.mp e12).resolve_right hω1'
  have z20 : h 2 0 = 0 := (mul_eq_zero.mp e20).resolve_right hω1''
  have z21 : h 2 1 = 0 := (mul_eq_zero.mp e21).resolve_right hω1''
  have hne22 : h 2 2 ≠ 0 := by
    rcases row_ne_zero3 hh 2 with h0 | h0 | h0
    · exact absurd z20 h0
    · exact absurd z21 h0
    · exact h0
  have B22 : h 2 2 * (ω ^ 2 - c₁ * ω ^ 2) = 0 := entry_eq_of_diag h₁ 2 2
  have hc1 : c₁ = 1 := by
    have hsub : ω ^ 2 - c₁ * ω ^ 2 = 0 := (mul_eq_zero.mp B22).resolve_left hne22
    have e : ω ^ 2 * (1 - c₁) = 0 := by linear_combination hsub
    have e' : 1 - c₁ = 0 := (mul_eq_zero.mp e).resolve_left (pow_ne_zero 2 hω0)
    linear_combination -e'
  have B01 : h 0 1 * (ω - c₁ * 1) = 0 := entry_eq_of_diag h₁ 0 1
  have B10 : h 1 0 * (1 - c₁ * ω) = 0 := entry_eq_of_diag h₁ 1 0
  have f01 : h 0 1 * (ω - 1) = 0 := by linear_combination B01 + h 0 1 * hc1
  have f10 : h 1 0 * (1 - ω) = 0 := by linear_combination B10 + h 1 0 * ω * hc1
  have z01 : h 0 1 = 0 := (mul_eq_zero.mp f01).resolve_right hω1'
  have z10 : h 1 0 = 0 := (mul_eq_zero.mp f10).resolve_right hω1''
  intro i j
  fin_cases i <;> fin_cases j <;> intro hij <;> first | exact (hij rfl).elim | assumption

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusDiag

end FusDiag

section FusEV


namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusEV

open Matrix CFSG.RankThree.PartTwo.Sec4

theorem conj_matrix {K : Type} [Field K] (g₀ : GL (Fin 3) K) (l d₀ d₁ d₂ : Kˣ) :
    ((g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits d₀ d₁ d₂) * g₀⁻¹ :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g₀ : Matrix (Fin 3) (Fin 3) K) *
        diagonal (fun i => (l : K) * (![(d₀ : K), (d₁ : K), (d₂ : K)] i)) *
        ((g₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagUnits, Matrix.scalar_apply,
    diagonal_mul_diagonal]

theorem mulVec_col_eig {K : Type} [Field K] (M N : Matrix (Fin 3) (Fin 3) K) (v : Fin 3 → K)
    (hNM : N * M = 1) (i : Fin 3) :
    (M * diagonal v * N) *ᵥ M.col i = v i • M.col i := by
  have h1 : (M * diagonal v * N) * M = M * diagonal v := by
    simp only [Matrix.mul_assoc, hNM, Matrix.mul_one]
  rw [← Matrix.col_mul_eq_mulVec_col, h1]
  funext r
  simp [Matrix.mul_diagonal, mul_comm]

theorem regular_eigen_of_conj {K : Type} [Field K] (g₀ : GL (Fin 3) K) (l d₀ d₁ d₂ : Kˣ)
    (h01 : d₀ ≠ d₁) (h02 : d₀ ≠ d₂) (h12 : d₁ ≠ d₂) :
    ∃ (b : Fin 3 → (Fin 3 → K)) (d : Fin 3 → K), LinearIndependent K b ∧ Function.Injective d ∧
      ∀ i, ((g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits d₀ d₁ d₂) * g₀⁻¹ :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d i • b i := by
  have hl : (l : K) ≠ 0 := l.ne_zero
  have h01' : (d₀ : K) ≠ (d₁ : K) := fun h => h01 (Units.ext h)
  have h02' : (d₀ : K) ≠ (d₂ : K) := fun h => h02 (Units.ext h)
  have h12' : (d₁ : K) ≠ (d₂ : K) := fun h => h12 (Units.ext h)
  have hinj : Function.Injective
      (fun i : Fin 3 => (l : K) * (![(d₀ : K), (d₁ : K), (d₂ : K)] i)) := by
    intro i j hij
    have h := mul_left_cancel₀ hl hij
    fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨(g₀ : Matrix (Fin 3) (Fin 3) K).col,
    fun i => (l : K) * (![(d₀ : K), (d₁ : K), (d₂ : K)] i), ?_, hinj, ?_⟩
  · exact Matrix.linearIndependent_cols_iff_isUnit.2 g₀.isUnit
  · intro i
    rw [conj_matrix]
    exact mulVec_col_eig _ _ _ (Units.inv_mul g₀) i

theorem conj_diag_comm {K : Type} [Field K] (g₀ : GL (Fin 3) K) (l s t β : Kˣ) :
    (g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g₀⁻¹) *
        (g₀ * diagUnits 1 β (β ^ 2) * g₀⁻¹) =
      (g₀ * diagUnits 1 β (β ^ 2) * g₀⁻¹) *
        (g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g₀⁻¹) := by
  have key : ∀ A B : GL (Fin 3) K, (g₀ * A * g₀⁻¹) * (g₀ * B * g₀⁻¹) = g₀ * (A * B) * g₀⁻¹ := by
    intro A B
    simp only [mul_assoc, inv_mul_cancel_left]
  have hD : Commute (diagUnits 1 s t) (diagUnits 1 β (β ^ 2)) := by
    show diagUnits 1 s t * diagUnits 1 β (β ^ 2) = diagUnits 1 β (β ^ 2) * diagUnits 1 s t
    rw [diagUnits_mul, diagUnits_mul, mul_comm s β, mul_comm t (β ^ 2)]
  have h1 : Commute (GeneralLinearGroup.scalar (Fin 3) l) (diagUnits 1 β (β ^ 2)) :=
    GeneralLinearGroup.scalar_commute l _
  have hc : Commute (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)
      (diagUnits 1 β (β ^ 2)) :=
    h1.mul_left hD
  rw [key, key, hc.eq]

theorem conj_diag_pow {K : Type} [Field K] (g₀ : GL (Fin 3) K) (l s t : Kˣ) (k : ℕ) :
    (g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g₀⁻¹) ^ k =
      g₀ * (GeneralLinearGroup.scalar (Fin 3) (l ^ k) * diagUnits 1 (s ^ k) (t ^ k)) * g₀⁻¹ := by
  have hD : ∀ n : ℕ, diagUnits (1 : Kˣ) s t ^ n = diagUnits 1 (s ^ n) (t ^ n) := by
    intro n
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_diagUnits, coe_diagUnits, diagonal_pow]
    congr 1
    funext i
    fin_cases i <;> simp [Units.val_pow_eq_pow_val]
  have hc : Commute (GeneralLinearGroup.scalar (Fin 3) l) (diagUnits 1 s t) :=
    GeneralLinearGroup.scalar_commute l _
  rw [conj_pow, hc.mul_pow, ← map_pow (GeneralLinearGroup.scalar (Fin 3)) l k, hD k]

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusEV

end FusEV

section FusTor


open CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusTor

theorem frobGL_diagUnits_fus {K : Type} [Field K] (σ : K ≃+* K) (a b c : Kˣ) :
    frobGL σ (diagUnits a b c) = diagUnits (Units.map (σ : K →* K) a)
      (Units.map (σ : K →* K) b) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  rw [coe_frobGL, coe_diagUnits, coe_diagUnits, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem mul_diagUnits_eq_diagUnits_mul {K : Type} [Field K] {M : GL (Fin 3) K}
    (hM : ∀ i j : Fin 3, i ≠ j → (M : Matrix (Fin 3) (Fin 3) K) i j = 0) (a b c : Kˣ) :
    M * diagUnits a b c = diagUnits a b c * M := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagUnits]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact mul_comm _ _
  · simp [Matrix.mul_diagonal, Matrix.diagonal_mul, hM i j hij]

theorem det_conj_fus {K : Type} [Field K] (g a : GL (Fin 3) K) :
    ((g * a * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (a : Matrix (Fin 3) (Fin 3) K).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

theorem det_scalar_fus {K : Type} [Field K] (u : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (u : K) ^ 3 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Fin.prod_univ_three]
  show (u : K) * (u : K) * (u : K) = (u : K) ^ 3
  ring

theorem scalar_eq_diagUnits_fus {K : Type} [Field K] (u : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) u = diagUnits u u u := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, coe_diagUnits, Matrix.scalar_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem bar_mul_eq_one_fus {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {a : Kˣ} (ha : a ^ (p ^ f + 1) = 1) : h.bar (a : K) * (a : K) = 1 := by
  rw [h.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ha, Units.val_one]

theorem diagUnits_mem_glPi_false {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {a b c : Kˣ} (ha : a ^ (p ^ f + 1) = 1) (hb : b ^ (p ^ f + 1) = 1)
    (hc : c ^ (p ^ f + 1) = 1) : diagUnits a b c ∈ glPi false 3 (p ^ f) K := by
  have ha' := bar_mul_eq_one_fus h ha
  have hb' := bar_mul_eq_one_fus h hb
  have hc' := bar_mul_eq_one_fus h hc
  rw [mem_glPi_false h, coe_diagUnits, Matrix.diagonal_map (map_zero h.bar),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [ha', hb', hc']

theorem fusion_identity {K : Type} [Field K] (σ : K ≃+* K) (g g₀ : GL (Fin 3) K) (β : Kˣ)
    (hh : ∀ i j : Fin 3, i ≠ j →
      ((g₀⁻¹ * g * frobGL σ g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    g * frobGL σ (g₀ * diagUnits 1 β (β ^ 2) * g₀⁻¹) * g⁻¹ =
      g₀ * diagUnits 1 (Units.map (σ : K →* K) β) (Units.map (σ : K →* K) β ^ 2) * g₀⁻¹ := by
  have hcomm := mul_diagUnits_eq_diagUnits_mul hh 1 (Units.map (σ : K →* K) β)
    (Units.map (σ : K →* K) β ^ 2)
  have hfrob : frobGL σ (diagUnits 1 β (β ^ 2)) =
      diagUnits 1 (Units.map (σ : K →* K) β) (Units.map (σ : K →* K) β ^ 2) := by
    rw [frobGL_diagUnits_fus, map_one, map_pow]
  set H : GL (Fin 3) K := g₀⁻¹ * g * frobGL σ g₀ with hH
  set D : GL (Fin 3) K := diagUnits 1 (Units.map (σ : K →* K) β)
    (Units.map (σ : K →* K) β ^ 2) with hD
  have hgg : g * frobGL σ g₀ = g₀ * H := by
    rw [hH]
    group
  rw [map_mul, map_mul, map_inv, hfrob]
  calc g * (frobGL σ g₀ * D * (frobGL σ g₀)⁻¹) * g⁻¹
      = (g * frobGL σ g₀) * D * (g * frobGL σ g₀)⁻¹ := by group
    _ = (g₀ * H) * D * (g₀ * H)⁻¹ := by rw [hgg]
    _ = g₀ * (H * D * H⁻¹) * g₀⁻¹ := by group
    _ = g₀ * (D * H * H⁻¹) * g₀⁻¹ := by rw [hcomm]
    _ = g₀ * D * g₀⁻¹ := by group

theorem torus_elt_mem_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) {g₀ : GL (Fin 3) K} (hg₀ : g₀ ∈ glPi π 3 (p ^ f) K) {β : Kˣ}
    (hβ : π = false → β ^ (p ^ f + 1) = 1) :
    GeneralLinearGroup.scalar (Fin 3) β⁻¹ * (g₀ * diagUnits 1 β (β ^ 2) * g₀⁻¹) ∈
      slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by
    subst h
    exact hK.unitary
  have hdet : ((GeneralLinearGroup.scalar (Fin 3) β⁻¹ * (g₀ * diagUnits 1 β (β ^ 2) * g₀⁻¹) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have hβ0 : (β : K) ≠ 0 := Units.ne_zero β
    have key : (β : K)⁻¹ ^ 3 * ((1 : K) * (β : K) * (β : K) ^ 2) = 1 := by
      calc (β : K)⁻¹ ^ 3 * ((1 : K) * (β : K) * (β : K) ^ 2)
          = ((β : K)⁻¹ * (β : K)) ^ 3 := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hβ0, one_pow]
    rw [Units.val_mul, Matrix.det_mul, det_conj_fus, det_scalar_fus, coe_diagUnits,
      Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using key
  have hgl : GeneralLinearGroup.scalar (Fin 3) β⁻¹ * (g₀ * diagUnits 1 β (β ^ 2) * g₀⁻¹) ∈
      glPi π 3 (p ^ f) K := by
    cases π
    · have hu : UnitaryFieldData p f K := hK.unitary
      have hb : β ^ (p ^ f + 1) = 1 := hβ rfl
      have hS : GeneralLinearGroup.scalar (Fin 3) β⁻¹ ∈ glPi false 3 (p ^ f) K := by
        rw [scalar_eq_diagUnits_fus]
        exact diagUnits_mem_glPi_false hu (by rw [inv_pow, hb, inv_one])
          (by rw [inv_pow, hb, inv_one]) (by rw [inv_pow, hb, inv_one])
      have hD : diagUnits 1 β (β ^ 2) ∈ glPi false 3 (p ^ f) K :=
        diagUnits_mem_glPi_false hu (by rw [one_pow]) hb
          (by rw [pow_right_comm, hb, one_pow])
      exact mul_mem hS (mul_mem (mul_mem hg₀ hD) (inv_mem hg₀))
    · exact mem_glPi_true _ _
  exact (mem_slPi_iff hπ).2 ⟨hgl, hdet⟩

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusTor

end FusTor

section FusCF


namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusCF

open CFSG.RankThree.PartTwo.Sec4 Matrix

theorem frobGL_diagUnits_map {K : Type} [Field K] (σ : K ≃+* K) (a b c : Kˣ) :
    frobGL σ (diagUnits a b c) = diagUnits (Units.map (σ : K →* K) a)
      (Units.map (σ : K →* K) b) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  rw [coe_frobGL, coe_diagUnits, coe_diagUnits, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem scalar_central_L3 {K : Type} [Field K] (u : Kˣ) (x : GL (Fin 3) K) :
    x * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * x :=
  (GeneralLinearGroup.scalar_commute u x).symm

theorem conj_scalar_of_fix {K : Type} [Field K] (σ : K ≃+* K) (g g₀ : GL (Fin 3) K) (l s t : Kˣ)
    (hs : Units.map (σ : K →* K) s = s) (ht : Units.map (σ : K →* K) t = t) {u : Kˣ}
    (hu : g * frobGL σ (g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g₀⁻¹) *
        g⁻¹ =
      (g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g₀⁻¹) *
        GeneralLinearGroup.scalar (Fin 3) u) :
    ∃ c : Kˣ, (g₀⁻¹ * g * frobGL σ g₀) * diagUnits 1 s t * (g₀⁻¹ * g * frobGL σ g₀)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) c * diagUnits 1 s t := by
  have hX : frobGL σ (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l) * diagUnits 1 s t := by
    rw [map_mul, frobGL_scalar, frobGL_diagUnits_map, map_one, hs, ht]
  obtain ⟨h', hh'⟩ : ∃ h' : GL (Fin 3) K, h' = g₀⁻¹ * g * frobGL σ g₀ := ⟨_, rfl⟩
  rw [← hh']
  have hL : g * frobGL σ (g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g₀⁻¹) *
      g⁻¹ = g₀ * (h' * (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l) *
        diagUnits 1 s t) * h'⁻¹) * g₀⁻¹ := by
    rw [map_mul, map_mul, map_inv, hX, hh']
    group
  have hcancel : h' * (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l) *
      diagUnits 1 s t) * h'⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t *
        GeneralLinearGroup.scalar (Fin 3) u := by
    have h1 : g₀ * (h' * (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l) *
        diagUnits 1 s t) * h'⁻¹) * g₀⁻¹ =
        g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t *
          GeneralLinearGroup.scalar (Fin 3) u) * g₀⁻¹ := by
      rw [← hL, hu]
      calc g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g₀⁻¹ *
            GeneralLinearGroup.scalar (Fin 3) u
          = g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) *
              (g₀⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) := by group
        _ = g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) *
              (GeneralLinearGroup.scalar (Fin 3) u * g₀⁻¹) := by
            rw [scalar_central_L3 u g₀⁻¹]
        _ = g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t *
              GeneralLinearGroup.scalar (Fin 3) u) * g₀⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  have hS : GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l) *
      (h' * diagUnits 1 s t * h'⁻¹) =
      GeneralLinearGroup.scalar (Fin 3) (l * u) * diagUnits 1 s t := by
    calc GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l) *
          (h' * diagUnits 1 s t * h'⁻¹)
        = (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l) * h') *
            diagUnits 1 s t * h'⁻¹ := by group
      _ = (h' * GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l)) *
            diagUnits 1 s t * h'⁻¹ := by
          rw [scalar_central_L3 (Units.map (σ : K →* K) l) h']
      _ = h' * (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l) *
            diagUnits 1 s t) * h'⁻¹ := by group
      _ = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t *
            GeneralLinearGroup.scalar (Fin 3) u := hcancel
      _ = GeneralLinearGroup.scalar (Fin 3) l * (diagUnits 1 s t *
            GeneralLinearGroup.scalar (Fin 3) u) := by group
      _ = GeneralLinearGroup.scalar (Fin 3) l * (GeneralLinearGroup.scalar (Fin 3) u *
            diagUnits 1 s t) := by rw [scalar_central_L3 u (diagUnits 1 s t)]
      _ = GeneralLinearGroup.scalar (Fin 3) (l * u) * diagUnits 1 s t := by
          rw [map_mul, mul_assoc]
  refine ⟨(Units.map (σ : K →* K) l)⁻¹ * (l * u), ?_⟩
  have hc : GeneralLinearGroup.scalar (Fin 3) ((Units.map (σ : K →* K) l)⁻¹ * (l * u)) =
      (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l))⁻¹ *
        GeneralLinearGroup.scalar (Fin 3) (l * u) := by
    simp only [map_mul, map_inv]
  rw [hc]
  calc h' * diagUnits 1 s t * h'⁻¹
      = (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l))⁻¹ *
          (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l) *
            (h' * diagUnits 1 s t * h'⁻¹)) := by group
    _ = (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l))⁻¹ *
          (GeneralLinearGroup.scalar (Fin 3) (l * u) * diagUnits 1 s t) := by rw [hS]
    _ = (GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) l))⁻¹ *
          GeneralLinearGroup.scalar (Fin 3) (l * u) * diagUnits 1 s t := by group

theorem regular_not_scalar {K : Type} [Field K] (g₀ : GL (Fin 3) K) (l ω : Kˣ) (hω : ω ≠ 1)
    {c : Kˣ}
    (h : g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 ω (ω ^ 2)) * g₀⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) c) : False := by
  have h1 : GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 ω (ω ^ 2) =
      GeneralLinearGroup.scalar (Fin 3) c := by
    calc GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 ω (ω ^ 2)
        = g₀⁻¹ * (g₀ * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 ω (ω ^ 2)) * g₀⁻¹) *
            g₀ := by group
      _ = g₀⁻¹ * GeneralLinearGroup.scalar (Fin 3) c * g₀ := by rw [h]
      _ = GeneralLinearGroup.scalar (Fin 3) c := by
          rw [scalar_central_L3 c g₀⁻¹]
          group
  have hD : diagUnits (1 : Kˣ) ω (ω ^ 2) = GeneralLinearGroup.scalar (Fin 3) (l⁻¹ * c) := by
    calc diagUnits (1 : Kˣ) ω (ω ^ 2)
        = (GeneralLinearGroup.scalar (Fin 3) l)⁻¹ *
            (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 ω (ω ^ 2)) := by group
      _ = (GeneralLinearGroup.scalar (Fin 3) l)⁻¹ * GeneralLinearGroup.scalar (Fin 3) c := by
          rw [h1]
      _ = GeneralLinearGroup.scalar (Fin 3) (l⁻¹ * c) := by
          simp only [map_mul, map_inv]
  have e0 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hD
  have e1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 1) hD
  simp only [coe_diagUnits, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one] at e0 e1
  exact hω (Units.ext (e1.trans e0.symm))

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusCF

end FusCF

