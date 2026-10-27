module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143Abs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143L3Defs
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.Open.StatedCenterThree
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UNorm

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

open Matrix CFSG.LieType.Universal.Unitary CFSG.Open.StatedCenterThree

section MatrixLemmas

variable {K : Type*} [Field K] (σ : K ≃+* K)

private theorem su3_conjTr_diagonal (d : Fin 3 → K) :
    conjTr σ (diagonal d) = diagonal fun i => σ (d i) := by
  rw [conjTr, diagonal_map (map_zero σ), diagonal_transpose]

private theorem su3_conjTr_apply {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    conjTr σ X i j = σ (X j i) := rfl

private theorem su3_conjTr_conjTr (hσ : ∀ x, σ (σ x) = x) (A : Matrix (Fin 3) (Fin 3) K) :
    conjTr σ (conjTr σ A) = A := by
  ext i j
  simp [conjTr, hσ]

private theorem su3_eq_diagonal_of_conj_eq {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hωσ : σ ω * ω = 1) {M : Matrix (Fin 3) (Fin 3) K}
    (h : conjTr σ (diagonal ![1, ω, ω ^ 2]) * M * diagonal ![1, ω, ω ^ 2] = M) :
    M = diagonal fun i => M i i := by
  have hσω : σ ω = ω ^ 2 := by
    calc σ ω = σ ω * ω ^ 3 := by rw [hω3, mul_one]
      _ = (σ ω * ω) * ω ^ 2 := by ring
      _ = ω ^ 2 := by rw [hωσ, one_mul]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have hlam : ∀ i : Fin 3, (![1, ω, ω ^ 2] : Fin 3 → K) i = ω ^ (i : ℕ) := by
    intro i
    fin_cases i <;> simp
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij]
    have h1 := congrFun (congrFun h i) j
    rw [su3_conjTr_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    simp only [hlam] at h1
    rw [map_pow, hσω, ← pow_mul] at h1
    have h2 : M i j * (ω ^ (2 * (i : ℕ) + (j : ℕ)) - 1) = 0 := by
      rw [pow_add]
      linear_combination h1
    have hne : ω ^ (2 * (i : ℕ) + (j : ℕ)) ≠ 1 := by
      intro h3
      have h4 := orderOf_dvd_of_pow_eq_one h3
      rw [hord] at h4
      have hi := i.2
      have hj := j.2
      have hij' : (i : ℕ) ≠ (j : ℕ) := fun e => hij (Fin.ext e)
      omega
    exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hne)

private theorem su3_exists_norm_triple {c : Fin 3 → K} (hc : ∀ i, c i ≠ 0)
    (hch : ∀ i, σ (c i) = c i) (hnorm : ∀ x : K, σ x = x → x ≠ 0 → ∃ s : K, σ s * s = x) :
    ∃ s0 s1 s2 : K, s0 * s1 * s2 = 1 ∧ σ s0 * s0 * c 2 = c 0 ∧ σ s1 * s1 * c 0 = c 1 ∧
      σ s2 * s2 * c 1 = c 2 := by
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  obtain ⟨s0, hs0⟩ := hnorm (c 0 / c 2) (by rw [map_div₀, hch, hch]) (div_ne_zero h0 h2)
  obtain ⟨s1, hs1⟩ := hnorm (c 1 / c 0) (by rw [map_div₀, hch, hch]) (div_ne_zero h1 h0)
  have hs0z : s0 ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at hs0
    exact div_ne_zero h0 h2 hs0.symm
  have hs1z : s1 ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at hs1
    exact div_ne_zero h1 h0 hs1.symm
  refine ⟨s0, s1, (s0 * s1)⁻¹, mul_inv_cancel₀ (mul_ne_zero hs0z hs1z), ?_, ?_, ?_⟩
  · rw [hs0]
    field_simp
  · rw [hs1]
    field_simp
  · have hn : σ s0 * σ s1 * (s0 * s1) = c 1 / c 2 := by
      calc σ s0 * σ s1 * (s0 * s1) = (σ s0 * s0) * (σ s1 * s1) := by ring
        _ = c 0 / c 2 * (c 1 / c 0) := by rw [hs0, hs1]
        _ = c 1 / c 2 := by field_simp
    rw [map_inv₀, map_mul, ← mul_inv, hn, inv_div]
    field_simp

private theorem su3_exists_monomial {ω : K} (hω3 : ω ^ 3 = 1) {c : Fin 3 → K}
    (hc : ∀ i, c i ≠ 0) (hch : ∀ i, σ (c i) = c i)
    (hnorm : ∀ x : K, σ x = x → x ≠ 0 → ∃ s : K, σ s * s = x) :
    ∃ C : Matrix (Fin 3) (Fin 3) K, C.det = 1 ∧
      C * diagonal ![1, ω, ω ^ 2] = ω • (diagonal ![1, ω, ω ^ 2] * C) ∧
      conjTr σ C * diagonal c * C = diagonal c := by
  obtain ⟨s0, s1, s2, hs, hn0, hn1, hn2⟩ := su3_exists_norm_triple σ hc hch hnorm
  refine ⟨!![0, s1, 0; 0, 0, s2; s0, 0, 0], ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_three]
    linear_combination hs
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply] <;>
      first | ring1 | linear_combination (-s0) * hω3
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply] <;>
      first | linear_combination hn0 | linear_combination hn1 | linear_combination hn2

private theorem su3_exists_conj_smul (hσ : ∀ x, σ (σ x) = x)
    (hnorm : ∀ x : K, σ x = x → x ≠ 0 → ∃ s : K, σ s * s = x)
    {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hωσ : σ ω * ω = 1)
    {A P Pi : Matrix (Fin 3) (Fin 3) K} (hAu : conjTr σ A * A = 1)
    (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) (hAP : A * P = P * diagonal ![1, ω, ω ^ 2]) :
    ∃ Y : Matrix (Fin 3) (Fin 3) K, Y.det = 1 ∧ conjTr σ Y * Y = 1 ∧
      Y * A = A * scalar (Fin 3) ω * Y := by
  have hM1 : conjTr σ (diagonal ![1, ω, ω ^ 2]) * (conjTr σ P * P) * diagonal ![1, ω, ω ^ 2] =
      conjTr σ P * P := by
    calc conjTr σ (diagonal ![1, ω, ω ^ 2]) * (conjTr σ P * P) * diagonal ![1, ω, ω ^ 2]
        = conjTr σ (P * diagonal ![1, ω, ω ^ 2]) * (P * diagonal ![1, ω, ω ^ 2]) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = conjTr σ (A * P) * (A * P) := by rw [hAP]
      _ = conjTr σ P * (conjTr σ A * A) * P := by simp only [conjTr_mul, Matrix.mul_assoc]
      _ = conjTr σ P * P := by rw [hAu, Matrix.mul_one]
  have hMd := su3_eq_diagonal_of_conj_eq σ hω3 hω1 hωσ hM1
  have hMh : conjTr σ (conjTr σ P * P) = conjTr σ P * P := by
    rw [conjTr_mul, su3_conjTr_conjTr σ hσ]
  have hch : ∀ i, σ ((conjTr σ P * P) i i) = (conjTr σ P * P) i i := fun i => by
    have := congrFun (congrFun hMh i) i
    rwa [su3_conjTr_apply] at this
  have hc : ∀ i, (conjTr σ P * P) i i ≠ 0 := fun i hi0 => by
    have hX : (Pi * conjTr σ Pi) * (conjTr σ P * P) = 1 := by
      calc (Pi * conjTr σ Pi) * (conjTr σ P * P) = Pi * (conjTr σ Pi * conjTr σ P) * P := by
            simp only [Matrix.mul_assoc]
        _ = Pi * conjTr σ (P * Pi) * P := by rw [conjTr_mul]
        _ = 1 := by rw [hPPi, conjTr_one, Matrix.mul_one, hPiP]
    have := congrFun (congrFun hX i) i
    rw [hMd, Matrix.mul_diagonal, Matrix.one_apply_eq] at this
    simp [hi0] at this
  obtain ⟨C, hCdet, hCD, hCM⟩ := su3_exists_monomial σ hω3 (c := fun i => (conjTr σ P * P) i i)
    hc hch hnorm
  have hcancel : ∀ X : Matrix (Fin 3) (Fin 3) K, Pi * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have hA : A = P * diagonal ![1, ω, ω ^ 2] * Pi := by
    calc A = A * (P * Pi) := by rw [hPPi, Matrix.mul_one]
      _ = (A * P) * Pi := by rw [Matrix.mul_assoc]
      _ = P * diagonal ![1, ω, ω ^ 2] * Pi := by rw [hAP]
  refine ⟨P * C * Pi, ?_, ?_, ?_⟩
  · calc (P * C * Pi).det = P.det * C.det * Pi.det := by rw [det_mul, det_mul]
      _ = C.det * (P * Pi).det := by rw [det_mul]; ring
      _ = 1 := by rw [hPPi, det_one, hCdet, mul_one]
  · calc conjTr σ (P * C * Pi) * (P * C * Pi)
        = conjTr σ Pi * (conjTr σ C * (conjTr σ P * P) * C) * Pi := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = conjTr σ Pi * (conjTr σ P * P) * Pi := by rw [hMd, hCM]
      _ = conjTr σ (P * Pi) * (P * Pi) := by simp only [conjTr_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPPi, conjTr_one, Matrix.one_mul]
  · calc P * C * Pi * A = P * (C * diagonal ![1, ω, ω ^ 2]) * Pi := by
          rw [hA]; simp only [Matrix.mul_assoc, hcancel]
      _ = P * (ω • (diagonal ![1, ω, ω ^ 2] * C)) * Pi := by rw [hCD]
      _ = ω • (A * (P * C * Pi)) := by
          rw [hA]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hcancel]
      _ = A * scalar (Fin 3) ω * (P * C * Pi) := by
          rw [scalar_apply, ← smul_eq_mul_diagonal, Matrix.smul_mul]

end MatrixLemmas

section GroupLemmas

private theorem su3_exists_scalar_of_central {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) {z : GL (Fin 3) K}
    (hz : ∀ g ∈ CFSG.Open.StatedSU 3 q K, g * z = z * g) :
    ∃ c : K, (z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
  have hq2 := two_le_of_card_eq_sq hK
  have hq : q ≠ 0 := by omega
  obtain ⟨a, ha⟩ := exists_orderOf_eq hK
  have haq : a ^ (q + 1) = 1 := ha ▸ pow_orderOf_eq_one a
  have ha1 : (a : K) ≠ 1 := fun h => by
    have : a = 1 := Units.ext h
    rw [this, orderOf_one] at ha
    omega
  have ha2 : (a : K) ≠ ((a⁻¹ : Kˣ) : K) := fun h => by
    have h' : a ^ 2 = 1 := by
      rw [sq]
      nth_rw 2 [Units.ext h]
      exact mul_inv_cancel a
    have := orderOf_dvd_of_pow_eq_one h'
    rw [ha] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hb1 : ((a⁻¹ : Kˣ) : K) ≠ 1 := fun h => ha1 (by
    have : a⁻¹ = 1 := Units.ext h
    rw [inv_eq_one.mp this, Units.val_one])
  have hinj : Function.Injective ![(a : K), ((a⁻¹ : Kˣ) : K), 1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hcomm : ∀ g ∈ CFSG.Open.StatedSU 3 q K,
      (g : Matrix (Fin 3) (Fin 3) K) * (z : Matrix (Fin 3) (Fin 3) K) =
        (z : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := fun g hg => by
    have := hz g hg
    exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) this
  set M : Matrix (Fin 3) (Fin 3) K := (z : Matrix (Fin 3) (Fin 3) K) with hMdef
  have hD := hcomm (diagGL a) (diagGL_mem hq haq)
  have hdiag := eq_diagonal_of_commute hinj hD.symm
  have hP := hcomm cyc3GL (cyc3GL_mem hq)
  change cyc3 * M = M * cyc3 at hP
  rw [hdiag] at hP
  obtain ⟨h1, h2⟩ := eq_of_diagonal_commute_cyc3 hP.symm
  refine ⟨M 0 0, ?_⟩
  rw [hdiag, Matrix.scalar_apply]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact h1
  · exact h2

private theorem su3_not_config {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (σ : K ≃+* K) (hσ : ∀ x, σ (σ x) = x)
    (hnorm : ∀ x : K, σ x = x → x ≠ 0 → ∃ s : K, σ s * s = x)
    (hmem : ∀ x : GL (Fin 3) K, x ∈ CFSG.Open.StatedSU 3 q K ↔
      (x : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
        conjTr σ (x : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) = 1)
    (heig : L143EigProp) (a w : CFSG.Open.StatedSU 3 q K) : ¬ L143Config a w := by
  intro h
  have hz : ∀ g ∈ CFSG.Open.StatedSU 3 q K, g * (w : GL (Fin 3) K) = (w : GL (Fin 3) K) * g :=
    fun g hg => congrArg Subtype.val (Subgroup.mem_center_iff.mp h.w_mem ⟨g, hg⟩)
  obtain ⟨ω, hωW⟩ := su3_exists_scalar_of_central hK hz
  have hW3 : ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    have := congrArg (fun x : CFSG.Open.StatedSU 3 q K =>
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h.w_pow
    simpa using this
  have hω3 : ω ^ 3 = 1 := by
    rw [hωW, ← map_pow (Matrix.scalar (Fin 3)) ω 3] at hW3
    exact Matrix.scalar_inj.mp (hW3.trans (map_one (Matrix.scalar (Fin 3))).symm)
  have hω1 : ω ≠ 1 := by
    rintro rfl
    apply h.w_ne
    apply Subtype.ext
    apply Units.ext
    rw [hωW]
    simp
  have hωσ : σ ω * ω = 1 := by
    have hu := ((hmem _).mp w.2).2
    rw [hωW, Matrix.scalar_apply, su3_conjTr_diagonal, diagonal_mul_diagonal] at hu
    have := congrFun (congrFun hu 0) 0
    simpa using this
  have hA3 : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    have := congrArg (fun x : CFSG.Open.StatedSU 3 q K =>
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h.a_pow
    simpa using this
  have hAns : ∀ c : K,
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c := by
    intro c hc
    apply h.a_not_mem
    rw [Subgroup.mem_center_iff]
    intro g
    have e : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hc]
      exact (Matrix.scalar_commute c (fun r => Commute.all c r) _).eq.symm
    exact Subtype.ext (Units.ext e)
  obtain ⟨P, hPdet, hAP⟩ := heig K ω hω3 hω1 _ hA3 ((hmem _).mp a.2).1 hAns
  obtain ⟨Y, hYdet, hYu, hYA⟩ := su3_exists_conj_smul σ hσ hnorm hω3 hω1 hωσ ((hmem _).mp a.2).2
    (Matrix.mul_nonsing_inv P hPdet) (Matrix.nonsing_inv_mul P hPdet) hAP
  have hYne : Y.det ≠ 0 := by rw [hYdet]; exact one_ne_zero
  have hyg : ((Matrix.GeneralLinearGroup.mkOfDetNeZero Y hYne : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = Y := Matrix.GeneralLinearGroup.val_mkOfDetNeZero Y hYne
  refine h.not_conj ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Y hYne,
    (hmem _).mpr ⟨by rw [hyg]; exact hYdet, by rw [hyg]; exact hYu⟩⟩ ?_
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  change ((Matrix.GeneralLinearGroup.mkOfDetNeZero Y hYne : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) * ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((w : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) * ((Matrix.GeneralLinearGroup.mkOfDetNeZero Y hYne :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [hyg, hωW]
  exact hYA

end GroupLemmas

theorem not_l143Config_statedSU (heig : L143EigProp) {p f : ℕ} [Fact p.Prime] {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    (a w : CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K) : ¬ L143Config a w := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p := charP_of_card_eq_prime_pow (f := 2 * f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    ring)
  refine su3_not_config hK (CFSG.LieType.BorelTits.unitaryInvolution K p f)
    (CFSG.LieType.BorelTits.unitaryInvolution_involutive hK) ?_ ?_ heig a w
  · intro c hc hc0
    obtain ⟨β, hβ⟩ := CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.exists_norm_eq hK
      (by rwa [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hc) hc0
    exact ⟨β, by rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]; exact hβ⟩
  · intro x
    rw [← SUid_eq_statedSU hK 3]
    exact mem_SUid

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
