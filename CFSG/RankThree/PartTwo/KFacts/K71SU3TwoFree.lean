module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
public import CFSG.RankThree.PartTwo.Sec8.Notation

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSU)
open Matrix

section Involution

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

theorem matrix_add_self {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : A + A = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem conjTr_add_one_of_unitary_involution {n : ℕ} {z : Matrix (Fin n) (Fin n) K}
    (hzu : conjTr σ z * z = 1) (hz2 : z * z = 1) :
    conjTr σ (z + 1) = z + 1 ∧ (z + 1) * (z + 1) = 0 := by
  have hN2 : (z + 1) * (z + 1) = 0 := by
    have e : (z + 1) * (z + 1) = (z + z) + (1 + 1) := by
      rw [add_mul, mul_add, mul_add, hz2, one_mul, mul_one, mul_one]
      abel
    rw [e, matrix_add_self, matrix_add_self, add_zero]
  have h1 : conjTr σ (z + 1) * (z + 1) + conjTr σ (z + 1) + (z + 1) = 0 := by
    have e : conjTr σ (z + 1) * (z + 1) + conjTr σ (z + 1) + (z + 1) =
        (conjTr σ z + conjTr σ z) + (z + z) + ((1 + 1) + (1 + 1)) := by
      rw [conjTr_add, conjTr_one, add_mul, mul_add, mul_add, hzu, mul_one, one_mul, one_mul]
      abel
    rw [e]
    simp only [matrix_add_self, add_zero]
  have h2 : conjTr σ (z + 1) * (z + 1) = 0 := by
    have h := congrArg (· * (z + 1)) h1
    simp only [add_mul, zero_mul, Matrix.mul_assoc, hN2, Matrix.mul_zero, zero_add,
      add_zero] at h
    exact h
  refine ⟨?_, hN2⟩
  rw [h2, zero_add] at h1
  calc conjTr σ (z + 1) = conjTr σ (z + 1) + (conjTr σ (z + 1) + (z + 1)) := by
        rw [h1, add_zero]
    _ = z + 1 := by rw [← add_assoc, matrix_add_self, zero_add]

end Involution

section Key

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

theorem eq_zero_of_entries {N : Matrix (Fin 3) (Fin 3) K} {d e : Fin 3 → K}
    (hd : ∀ i k, i ≠ k → d k * e i + d i * e k = 1)
    (hh : ∀ i j, σ (N j i) = N i j)
    (hsq : ∀ i j, ∑ k, N i k * N k j = 0)
    (hcom : ∀ i, ∑ k, N i k * (d k * N k i * e i) = ∑ k, d i * N i k * e k * N k i) :
    N = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hnorm : ∀ x : K, x * σ x = 0 → x = 0 := fun x hx => by
    rcases mul_eq_zero.1 hx with h | h
    · exact h
    · exact (map_eq_zero σ).1 h
  have h01 : d 1 * e 0 + d 0 * e 1 = 1 := hd 0 1 (by decide)
  have h02 : d 2 * e 0 + d 0 * e 2 = 1 := hd 0 2 (by decide)
  have h12 : d 2 * e 1 + d 1 * e 2 = 1 := hd 1 2 (by decide)
  have c0 := hcom 0
  have c1 := hcom 1
  have c2 := hcom 2
  simp only [Fin.sum_univ_three] at c0 c1 c2
  have s00 := hsq 0 0
  have s11 := hsq 1 1
  have s22 := hsq 2 2
  have s01 := hsq 0 1
  have s02 := hsq 0 2
  have s12 := hsq 1 2
  simp only [Fin.sum_univ_three] at s00 s11 s22 s01 s02 s12
  have E0 : N 0 1 * N 1 0 + N 0 2 * N 2 0 = 0 := by
    linear_combination (N 0 1 * N 1 0) * h01 + (N 0 2 * N 2 0) * h02 - c0 +
      (N 0 1 * N 1 0 + N 0 2 * N 2 0 - N 0 1 * N 1 0 * (d 0 * e 1) -
        N 0 2 * N 2 0 * (d 0 * e 2)) * h2
  have E1 : N 1 0 * N 0 1 + N 1 2 * N 2 1 = 0 := by
    linear_combination (N 1 0 * N 0 1) * h01 + (N 1 2 * N 2 1) * h12 - c1 +
      (N 1 0 * N 0 1 - N 1 0 * N 0 1 * d 1 * e 0 + N 1 2 * N 2 1 - N 1 2 * N 2 1 * d 1 * e 2) * h2
  have E2 : N 2 0 * N 0 2 + N 2 1 * N 1 2 = 0 := by
    linear_combination (N 2 0 * N 0 2) * h02 + (N 2 1 * N 1 2) * h12 - c2 +
      (N 2 0 * N 0 2 - N 2 0 * N 0 2 * d 2 * e 0 + N 2 1 * N 1 2 - N 2 1 * N 1 2 * d 2 * e 1) * h2
  have n00 : N 0 0 = 0 := mul_self_eq_zero.1 (by linear_combination s00 - E0)
  have n11 : N 1 1 = 0 := mul_self_eq_zero.1 (by linear_combination s11 - E1)
  have n22 : N 2 2 = 0 := mul_self_eq_zero.1 (by linear_combination s22 - E2)
  simp only [n00, n11, n22, zero_mul, mul_zero, zero_add, add_zero] at s01 s02 s12
  have e10 : N 1 0 = σ (N 0 1) := (hh 1 0).symm
  have e20 : N 2 0 = σ (N 0 2) := (hh 2 0).symm
  have e21 : N 2 1 = σ (N 1 2) := (hh 2 1).symm
  rw [e10, e20] at E0
  rw [e10, e21] at E1
  rw [e20, e21] at E2
  have hb : ∀ {a b : K}, a * σ a + b * σ b = 0 → a = 0 → b = 0 := fun h ha => by
    rw [ha, zero_mul, zero_add] at h
    exact hnorm _ h
  have hac : N 0 1 = 0 ∧ N 0 2 = 0 ∧ N 1 2 = 0 := by
    rcases mul_eq_zero.1 s02 with ha | hc
    · have hb' : N 0 2 = 0 := hb E0 ha
      refine ⟨ha, hb', ?_⟩
      have h3 : σ (N 0 2) * N 0 2 + σ (N 1 2) * N 1 2 = 0 := E2
      rw [hb', map_zero, zero_mul, zero_add, mul_comm] at h3
      exact hnorm _ h3
    · have h1 : σ (N 0 1) * N 0 1 + N 1 2 * σ (N 1 2) = 0 := E1
      rw [hc, map_zero, mul_zero, add_zero, mul_comm] at h1
      have ha : N 0 1 = 0 := hnorm _ h1
      exact ⟨ha, hb E0 ha, hc⟩
  obtain ⟨ha, hb', hc⟩ := hac
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n00, n11, n22, ha, hb', hc, e10, e20, e21]

theorem eq_one_of_commute_conj_diagonal {d e : Fin 3 → K} (hde : ∀ i, d i * e i = 1)
    (hd : ∀ i k, i ≠ k → d k * e i + d i * e k = 1) {z : Matrix (Fin 3) (Fin 3) K}
    (hzu : conjTr σ z * z = 1) (hz2 : z * z = 1)
    (hc : z * (diagonal d * z * diagonal e) = (diagonal d * z * diagonal e) * z) : z = 1 := by
  obtain ⟨hNh, hN2⟩ := conjTr_add_one_of_unitary_involution σ hzu hz2
  set N := z + 1 with hNdef
  have hz : z = N + 1 := by rw [hNdef, add_assoc, matrix_add_self, add_zero]
  have hDE : diagonal d * diagonal e = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext hde)
  set M := diagonal d * N * diagonal e with hM
  have hcN : N * M = M * N := by
    have e1 : diagonal d * z * diagonal e = M + 1 := by
      rw [hz, mul_add, add_mul, Matrix.mul_one, hDE]
    rw [e1, hz] at hc
    have e3 : (N + 1) * (M + 1) = N * M + (N + M + 1) := by noncomm_ring
    have e4 : (M + 1) * (N + 1) = M * N + (N + M + 1) := by noncomm_ring
    exact add_right_cancel (e3.symm.trans (hc.trans e4))
  have hh : ∀ i j, σ (N j i) = N i j := fun i j => by
    have := congrFun (congrFun hNh i) j
    simpa [conjTr] using this
  have hsq : ∀ i j, ∑ k, N i k * N k j = 0 := fun i j => by
    have := congrFun (congrFun hN2 i) j
    simpa [Matrix.mul_apply] using this
  have hMe : ∀ k i, M k i = d k * N k i * e i := fun k i => by
    rw [hM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hcom : ∀ i, ∑ k, N i k * (d k * N k i * e i) = ∑ k, d i * N i k * e k * N k i := by
    intro i
    have := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A i i) hcN
    simp only [Matrix.mul_apply, hMe] at this
    exact this
  have hN0 := eq_zero_of_entries σ hd hh hsq hcom
  rw [hz, hN0, zero_add]

end Key

section Diagonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem eq_bot_of_normalizes_diagonal {X : Subgroup (GL (Fin 3) K)}
    (hXu : ∀ x ∈ X, conjTr σ ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x = 1)
    (h2 : IsPGroup 2 X) {D : GL (Fin 3) K} {d e : Fin 3 → K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hDinv : ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal e)
    (hd : ∀ i k, i ≠ k → d k * e i + d i * e k = 1)
    (hXD : ∀ x ∈ X, D * x * D⁻¹ ∈ X) : X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hde : ∀ i, d i * e i = 1 := fun i => by
    have h0 : (D : Matrix (Fin 3) (Fin 3) K) * ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hD, hDinv, diagonal_mul_diagonal] at h0
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A i i) h0
    simpa using h
  by_contra hne
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hne
  have hZ := h2.center_nontrivial
  have h2Z : IsPGroup 2 (Subgroup.center X) := h2.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center X) := by
    rcases h2Z.card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne'
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set z' : X := (z : X) with hz'
  have hz'2 : z' * z' = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz, sq] at h
    exact congrArg Subtype.val h
  have hz'1 : z' ≠ 1 := by
    intro h1
    have h : z = 1 := Subtype.ext h1
    rw [h, orderOf_one] at hz
    norm_num at hz
  set w : X := ⟨D * z' * D⁻¹, hXD _ z'.2⟩ with hw
  have hzw : z' * w = w * z' := (Subgroup.mem_center_iff.1 z.2 w).symm
  have hmat : ((z' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (diagonal d * (z' : GL (Fin 3) K) * diagonal e) =
      (diagonal d * (z' : GL (Fin 3) K) * diagonal e) * (z' : GL (Fin 3) K) := by
    have h := congrArg (fun x : X => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hzw
    simp only [hw, Subgroup.coe_mul, Units.val_mul, hD, hDinv] at h
    exact h
  have hmat2 : ((z' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((z' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have h := congrArg (fun x : X => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hz'2
    simpa using h
  have h1 := eq_one_of_commute_conj_diagonal σ hde hd (hXu _ z'.2) hmat2 hmat
  apply hz'1
  exact Subtype.ext (Units.ext h1)

end Diagonal

section Main

variable {f : ℕ} {K : Type} [Field K]

theorem exists_primitive_cube_root (hK : PiField false 2 f K) :
    ∃ τ : K, τ ^ 3 = 1 ∧ τ ≠ 1 := by
  have := hK.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK.card, piCard, Bool.cond_false, ← pow_mul, mul_comm, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨u, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  · intro h1
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    norm_num at hu

theorem exists_unitary_diagonal (hK : PiField false 2 f K) (hq : ModThree false (2 ^ f))
    {v : GL (Fin 3) K} (hv : v ∈ StatedSU 3 (2 ^ f) K) (hv3 : v ^ 3 = 1)
    (hvs : ∀ c : K, (v : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) :
    ∃ (g : GL (Fin 3) K) (d e : Fin 3 → K), g ∈ glPi false 3 (2 ^ f) K ∧
      (v : Matrix (Fin 3) (Fin 3) K) * g = g * diagonal d ∧ (∀ i, d i * e i = 1) ∧
      ∀ i k, i ≠ k → d k * e i + d i * e k = 1 := by
  have := hK.finite
  have : CharP K 2 := hK.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : K) ≠ 0 := by
    rw [show (3 : K) = 1 by linear_combination h2]
    exact one_ne_zero
  set h := hK.unitary
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K 2 f
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (by rw [hK.card]; rfl)
  obtain ⟨τ, hτ3, hτ1⟩ := exists_primitive_cube_root hK
  have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτ3; norm_num at hτ3
  have hτsq : τ ^ 2 + τ + 1 = 0 := by
    have h' : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ3
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hτ1)
  obtain ⟨hdet, hvu⟩ := (mem_slPi_false h).1 hv
  have hvu' : conjTr σ (v : Matrix (Fin 3) (Fin 3) K) * v = 1 := by
    rw [conjTr_unitaryInvolution_eq hK]
    exact hvu
  have hy3 : (v : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hv3, Units.val_one]
  obtain ⟨g, j, hg, hform⟩ := exists_normal_form hτ3 hτ1 h3 hy3 hvs
  have hgdet : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp hg).ne_zero
  have hdetD : ∀ {D : Matrix (Fin 3) (Fin 3) K},
      (τ ^ (j : ℕ) • (v : Matrix (Fin 3) (Fin 3) K)) * g = g * D → D.det = 1 := by
    intro D hD
    have h1 := congrArg Matrix.det hD
    rw [det_mul, det_mul, det_smul, hdet, Fintype.card_fin, mul_one, ← pow_mul,
      mul_comm (j : ℕ) 3, pow_mul, hτ3, one_pow, one_mul] at h1
    exact (mul_right_eq_self₀.1 h1.symm).resolve_right hgdet
  rcases hform with hD | hD | hD
  swap
  · exfalso
    have h1 := hdetD hD
    rw [det_diagonal, Fin.prod_univ_three] at h1
    simp at h1
    exact hτ1 h1
  swap
  · exfalso
    have h1 := hdetD hD
    rw [det_diagonal, Fin.prod_univ_three] at h1
    change τ ^ 2 * 1 * 1 = 1 at h1
    rw [mul_one, mul_one] at h1
    exact hτ1 (by linear_combination hτ3 - τ * h1)
  set c : K := (τ ^ (j : ℕ))⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (pow_ne_zero _ hτ0)
  set d : Fin 3 → K := fun i => c * ![τ, τ ^ 2, 1] i with hd
  set e : Fin 3 → K := fun i => c⁻¹ * ![τ ^ 2, τ, 1] i with he
  have hyg : (v : Matrix (Fin 3) (Fin 3) K) * g = g * diagonal d := by
    have h1 : (v : Matrix (Fin 3) (Fin 3) K) * g = c • (g * diagonal ![τ, τ ^ 2, 1]) := by
      rw [← hD, Matrix.smul_mul, smul_smul, hc, inv_mul_cancel₀ (pow_ne_zero _ hτ0), one_smul]
    rw [h1, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    rfl
  have hτn : σ τ * τ = 1 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ]
    exact pow_succ_eq_one_of_modThree hq hτ3
  have hcn : σ c * c = 1 := by
    rw [hc, map_inv₀, map_pow, ← mul_inv, ← mul_pow, hτn, one_pow, inv_one]
  have hdσ : ∀ i, σ (d i) * d i = 1 := by
    intro i
    fin_cases i
    · change σ (c * τ) * (c * τ) = 1
      rw [map_mul]
      linear_combination (σ τ * τ) * hcn + hτn
    · change σ (c * τ ^ 2) * (c * τ ^ 2) = 1
      rw [map_mul, map_pow]
      linear_combination (σ τ * τ) ^ 2 * hcn + (σ τ * τ + 1) * hτn
    · change σ (c * 1) * (c * 1) = 1
      rw [mul_one, hcn]
  have hdist : d 0 ≠ d 1 ∧ d 0 ≠ d 2 ∧ d 1 ≠ d 2 := by
    refine ⟨fun h01 => ?_, fun h02 => ?_, fun h12 => ?_⟩
    · have h' : c * τ = c * τ ^ 2 := h01
      have : τ = τ ^ 2 := mul_left_cancel₀ hc0 h'
      apply hτ1
      have h'' : τ * τ = τ * 1 := by rw [← sq, ← this, mul_one]
      exact mul_left_cancel₀ hτ0 h''
    · have h' : c * τ = c * 1 := h02
      exact hτ1 (mul_left_cancel₀ hc0 h')
    · have h' : c * τ ^ 2 = c * 1 := h12
      have : τ ^ 2 = 1 := mul_left_cancel₀ hc0 h'
      exact hτ1 (by linear_combination hτ3 - τ * this)
  obtain ⟨g', hg'u, hyg'⟩ := exists_unitary_conj hσ hdσ (Or.inl hdist) hvu' hg hyg
  have hg' : IsUnit g' :=
    (Matrix.isUnit_iff_isUnit_det g').mpr (Matrix.isUnit_det_of_left_inverse hg'u)
  refine ⟨hg'.unit, d, e, ?_, by rw [IsUnit.unit_spec]; exact hyg', fun i => ?_, ?_⟩
  · rw [mem_glPi_false h, IsUnit.unit_spec, ← conjTr_unitaryInvolution_eq hK]
    exact hg'u
  · fin_cases i
    · change c * τ * (c⁻¹ * τ ^ 2) = 1
      rw [show c * τ * (c⁻¹ * τ ^ 2) = (c * c⁻¹) * τ ^ 3 by ring, mul_inv_cancel₀ hc0, hτ3,
        one_mul]
    · change c * τ ^ 2 * (c⁻¹ * τ) = 1
      rw [show c * τ ^ 2 * (c⁻¹ * τ) = (c * c⁻¹) * τ ^ 3 by ring, mul_inv_cancel₀ hc0, hτ3,
        one_mul]
    · change c * 1 * (c⁻¹ * 1) = 1
      rw [mul_one, mul_one, mul_inv_cancel₀ hc0]
  · intro i k hik
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · change c * τ ^ 2 * (c⁻¹ * τ ^ 2) + c * τ * (c⁻¹ * τ) = 1
      linear_combination (τ ^ 4 + τ ^ 2) * hcc + τ * hτ3 + hτsq - h2
    · change c * 1 * (c⁻¹ * τ ^ 2) + c * τ * (c⁻¹ * 1) = 1
      linear_combination (τ ^ 2 + τ) * hcc + hτsq - h2
    · change c * τ * (c⁻¹ * τ) + c * τ ^ 2 * (c⁻¹ * τ ^ 2) = 1
      linear_combination (τ ^ 4 + τ ^ 2) * hcc + τ * hτ3 + hτsq - h2
    · exact absurd rfl hik
    · change c * 1 * (c⁻¹ * τ) + c * τ ^ 2 * (c⁻¹ * 1) = 1
      linear_combination (τ ^ 2 + τ) * hcc + hτsq - h2
    · change c * τ * (c⁻¹ * 1) + c * 1 * (c⁻¹ * τ ^ 2) = 1
      linear_combination (τ ^ 2 + τ) * hcc + hτsq - h2
    · change c * τ ^ 2 * (c⁻¹ * 1) + c * 1 * (c⁻¹ * τ) = 1
      linear_combination (τ ^ 2 + τ) * hcc + hτsq - h2
    · exact absurd rfl hik

theorem eq_bot_of_normalizes (hK : PiField false 2 f K) (hq : ModThree false (2 ^ f))
    {v : GL (Fin 3) K} (hv : v ∈ StatedSU 3 (2 ^ f) K) (hv3 : v ^ 3 = 1)
    (hvs : ∀ c : K, (v : Matrix (Fin 3) (Fin 3) K) ≠ c • 1)
    {X : Subgroup (GL (Fin 3) K)} (hXu : X ≤ glPi false 3 (2 ^ f) K) (h2 : IsPGroup 2 X)
    (hXv : ∀ x ∈ X, v * x * v⁻¹ ∈ X) : X = ⊥ := by
  have := hK.finite
  have : CharP K 2 := hK.charP
  set h := hK.unitary
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K 2 f
  obtain ⟨g, d, e, hgU, hvg, hde, hd⟩ := exists_unitary_diagonal hK hq hv hv3 hvs
  set D : GL (Fin 3) K := g⁻¹ * v * g with hDdef
  have hDd : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    rw [hDdef, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hvg, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hDe : ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal e := by
    have hde' : diagonal d * diagonal e = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext hde)
    calc ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((D : Matrix (Fin 3) (Fin 3) K) *
          diagonal e) := by rw [hDd, hde', Matrix.mul_one]
      _ = diagonal e := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  set X' := X.map (MulAut.conj g⁻¹).toMonoidHom with hX'
  have hconjU : ∀ x ∈ X, g⁻¹ * x * g ∈ glPi false 3 (2 ^ f) K := fun x hx =>
    mul_mem (mul_mem (inv_mem hgU) (hXu hx)) hgU
  have hXu' : ∀ x ∈ X', conjTr σ ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (mem_glPi_false h).1 (hconjU x hx)
    rw [← conjTr_unitaryInvolution_eq hK] at h1
    simpa [MulAut.conj_apply, mul_assoc] using h1
  have h2' : IsPGroup 2 X' := h2.map _
  have hXD : ∀ x ∈ X', D * x * D⁻¹ ∈ X' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨v * x * v⁻¹, hXv x hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hDdef]
    group
  have hX'bot := eq_bot_of_normalizes_diagonal σ hXu' h2' hDd hDe hd hXD
  rw [eq_bot_iff]
  intro x hx
  have hx' : g⁻¹ * x * g ∈ X' := ⟨x, hx, by simp [mul_assoc]⟩
  rw [hX'bot, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [hx', mul_one, mul_inv_cancel]

end Main

section Bar

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {f : ℕ} {K : Type} [Field K]

theorem not_invTwoBarNontrivial_of_inducedAutHom_eq_conj (hK : PiField false 2 f K)
    (hq : ModThree false (2 ^ f))
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedSU 3 (2 ^ f) K) {b : G} (hbA : b ∈ A)
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (w : StatedSU 3 (2 ^ f) K) (hw3 : w ^ 3 = 1)
    (hws : ∀ c : K, ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1)
    (hbw : inducedAutHom L e ⟨b, hb⟩ = MulAut.conj w) : ¬ Sec8.InvTwoBarNontrivial A L := by
  rintro ⟨X, hX1, hX2, hXinv⟩
  have hτ : thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) ∈ autThetaQuot A L :=
    mem_autThetaQuot_iff.2 ⟨b, hb, hbA, rfl⟩
  set Y : Subgroup (GL (Fin 3) K) :=
    (X.map e.toMonoidHom).map (StatedSU 3 (2 ^ f) K).subtype with hY
  have hYu : Y ≤ glPi false 3 (2 ^ f) K := by
    rintro _ ⟨y, -, rfl⟩
    exact slPi_le_glPi (π := false) (fun _ => hK.unitary) y.2
  have hY2 : IsPGroup 2 Y := (hX2.map _).map _
  have hYw : ∀ y ∈ Y, (w : GL (Fin 3) K) * y * (w : GL (Fin 3) K)⁻¹ ∈ Y := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) x), ⟨_, hXinv _ hτ x hx, rfl⟩,
      ?_⟩
    have h1 : e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) x) =
        inducedAutHom L e ⟨b, hb⟩ (e x) := by
      rw [inducedAutHom_apply]
      simp [MulAut.congr_apply, compAction]
    rw [h1, hbw, MulAut.conj_apply]
    simp
  have hwmem : (w : GL (Fin 3) K) ∈ StatedSU 3 (2 ^ f) K := w.2
  have hw3' : (w : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hw3, Subgroup.coe_one]
  have hYbot := eq_bot_of_normalizes hK hq hwmem hw3' hws hYu hY2 hYw
  apply hX1
  rw [eq_bot_iff]
  intro x hx
  have hy : ((e x : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) ∈ Y := ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  rw [hYbot, Subgroup.mem_bot] at hy
  rw [Subgroup.mem_bot]
  have h1 : e x = 1 := Subtype.ext hy
  exact (map_eq_one_iff e e.injective).1 h1

end Bar

end CFSG.RankThree.PartTwo.KFacts
