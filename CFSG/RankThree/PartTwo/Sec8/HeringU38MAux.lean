module

import CFSG.RankThree.PartTwo.KFacts.K71PSU3
import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.GH74.KGroups

section Regular

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

@[expose] noncomputable def adjM (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  (M.map h.bar)ᵀ

theorem adjM_mul (M N : Matrix (Fin 3) (Fin 3) K) : adjM h (M * N) = adjM h N * adjM h M := by
  simp only [adjM, Matrix.map_mul, Matrix.transpose_mul]

theorem adjM_add (M N : Matrix (Fin 3) (Fin 3) K) : adjM h (M + N) = adjM h M + adjM h N := by
  ext i j
  simp [adjM]

theorem adjM_smul (c : K) (M : Matrix (Fin 3) (Fin 3) K) :
    adjM h (c • M) = h.bar c • adjM h M := by
  ext i j
  simp [adjM]

theorem adjM_one : adjM h (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  simp [adjM, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]

@[expose] def cycMat (B : Matrix (Fin 3) (Fin 3) K) (u : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => ![u, B *ᵥ u, B *ᵥ (B *ᵥ u)] j i

theorem cycMat_mulVec (B : Matrix (Fin 3) (Fin 3) K) (u z : Fin 3 → K) :
    cycMat B u *ᵥ z = z 0 • u + z 1 • (B *ᵥ u) + z 2 • (B *ᵥ (B *ᵥ u)) := by
  ext i
  simp [cycMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem indep_of_cyc {B : Matrix (Fin 3) (Fin 3) K} {u : Fin 3 → K}
    (hu : (cycMat B u).det ≠ 0) {a b d : K}
    (habd : a • (1 : Matrix (Fin 3) (Fin 3) K) + b • B + d • (B * B) = 0) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  have h1 : cycMat B u *ᵥ ![a, b, d] = 0 := by
    rw [cycMat_mulVec]
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M *ᵥ u) habd
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec,
      ← Matrix.mulVec_mulVec] at this
    simpa using this
  have h2 := Matrix.eq_zero_of_mulVec_eq_zero hu h1
  exact ⟨congrFun h2 0, congrFun h2 1, congrFun h2 2⟩

theorem exists_poly {B y : Matrix (Fin 3) (Fin 3) K} {u : Fin 3 → K}
    (hu : (cycMat B u).det ≠ 0) (hyB : y * B = B * y) :
    ∃ a b d : K, y = a • (1 : Matrix (Fin 3) (Fin 3) K) + b • B + d • (B * B) := by
  have hU : IsUnit (cycMat B u).det := isUnit_iff_ne_zero.mpr hu
  have hsolve : ∀ v : Fin 3 → K, ∃ z : Fin 3 → K, cycMat B u *ᵥ z = v := fun v =>
    ⟨(cycMat B u)⁻¹ *ᵥ v, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]⟩
  obtain ⟨z, hz⟩ := hsolve (y *ᵥ u)
  set P : Matrix (Fin 3) (Fin 3) K :=
    z 0 • (1 : Matrix (Fin 3) (Fin 3) K) + z 1 • B + z 2 • (B * B) with hP
  refine ⟨z 0, z 1, z 2, ?_⟩
  have hPu : P *ᵥ u = y *ᵥ u := by
    rw [← hz, cycMat_mulVec, hP]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  have hPB : P * B = B * P := by
    simp only [hP, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc]
  have hyk : ∀ k : ℕ, y *ᵥ ((B ^ k) *ᵥ u) = P *ᵥ ((B ^ k) *ᵥ u) := by
    intro k
    have hyBk : y * B ^ k = B ^ k * y := (Commute.pow_right (show Commute y B from hyB) k).eq
    have hPBk : P * B ^ k = B ^ k * P := (Commute.pow_right (show Commute P B from hPB) k).eq
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hyBk, hPBk, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hPu]
  have hall : ∀ v : Fin 3 → K, y *ᵥ v = P *ᵥ v := by
    intro v
    obtain ⟨w, rfl⟩ := hsolve v
    rw [cycMat_mulVec]
    have e0 := hyk 0
    have e1 := hyk 1
    have e2 := hyk 2
    simp only [pow_zero, Matrix.one_mulVec, pow_one, pow_two, ← Matrix.mulVec_mulVec] at e0 e1 e2
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, e0, e1, e2]
  exact Matrix.ext_of_mulVec_single fun i => hall _

theorem exists_eigenvector_root {B : Matrix (Fin 3) (Fin 3) K} {c : K} {u₀ : Fin 3 → K}
    (hu : (cycMat B u₀).det ≠ 0) (hB3 : B * B * B = c • (1 : Matrix (Fin 3) (Fin 3) K)) {l : K}
    (hl : l ^ 3 = c) : ∃ v : Fin 3 → K, v ≠ 0 ∧ B *ᵥ v = l • v := by
  set Q : Matrix (Fin 3) (Fin 3) K := B * B + l • B + (l ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K)
    with hQ
  have hQ0 : Q ≠ 0 := by
    intro h0
    have h1 := indep_of_cyc hu (a := l ^ 2) (b := l) (d := 1)
      (by rw [← h0, hQ, one_smul]; abel)
    exact one_ne_zero h1.2.2
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → K, Q *ᵥ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ0 (Matrix.ext_of_mulVec_single fun i => by rw [hcon, Matrix.zero_mulVec])
  refine ⟨Q *ᵥ w, hw, ?_⟩
  have hBBB : B * (B * B) = l ^ 3 • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Matrix.mul_assoc, hB3, hl]
  have hBQ : B * Q = l • Q := by
    simp only [hQ, mul_add, Matrix.mul_smul, Matrix.mul_one, hBBB, smul_add, smul_smul]
    module
  rw [Matrix.mulVec_mulVec, hBQ, Matrix.smul_mulVec]

theorem eigen_eta {B y : Matrix (Fin 3) (Fin 3) K} {c : K} (hB : adjM h B * B = 1)
    (hB3 : B * B * B = c • (1 : Matrix (Fin 3) (Fin 3) K)) {l : K} (hl9 : l ^ 9 = 1)
    (hl3 : l ^ 3 = c) {v : Fin 3 → K} (hv : v ≠ 0) (hBv : B *ᵥ v = l • v) {a b d : K}
    (hyp : y = a • (1 : Matrix (Fin 3) (Fin 3) K) + b • B + d • (B * B))
    (hy : adjM h y * y = 1) (hy7 : y ^ 7 = 1) : a + b * l + d * l ^ 2 = 1 := by
  haveI := h.charP
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl9
  have hc0 : c ≠ 0 := by
    rw [← hl3]
    exact pow_ne_zero _ hl0
  set η : K := a + b * l + d * l ^ 2 with hη
  have hyv : y *ᵥ v = η • v := by
    rw [hyp]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hBv, Matrix.mulVec_smul, smul_smul, hη]
    module
  have hypow : ∀ n : ℕ, (y ^ n) *ᵥ v = η ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hyv, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
      rw [mul_comm]
  have hη7 : η ^ 7 = 1 := by
    have h1 := hypow 7
    rw [hy7, Matrix.one_mulVec] at h1
    have h2 : (η ^ 7 - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv
  have hBBadj : B * B = c • adjM h B := by
    have h1 : adjM h B * (B * B * B) = c • adjM h B := by
      rw [hB3, Matrix.mul_smul, Matrix.mul_one]
    have h2 : adjM h B * (B * B * B) = B * B := by
      calc adjM h B * (B * B * B) = (adjM h B * B) * B * B := by simp only [Matrix.mul_assoc]
        _ = B * B := by rw [hB, Matrix.one_mul]
    rw [← h2, h1]
  have hbar : h.bar l * c = l ^ 2 := by
    rw [h.bar_apply, ← hl3]
    have : l ^ 11 = l ^ 2 := by
      calc l ^ 11 = l ^ 9 * l ^ 2 := by ring
        _ = l ^ 2 := by rw [hl9, one_mul]
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← this]
    ring
  have hadjBv : adjM h B *ᵥ v = h.bar l • v := by
    have h1 : (B * B) *ᵥ v = (l ^ 2) • v := by
      rw [← Matrix.mulVec_mulVec, hBv, Matrix.mulVec_smul, hBv, smul_smul, pow_two]
    have h2 : c • (adjM h B *ᵥ v) = (l ^ 2) • v := by
      rw [← Matrix.smul_mulVec, ← hBBadj, h1]
    have h3 : c • (adjM h B *ᵥ v) = c • (h.bar l • v) := by
      rw [h2, smul_smul, mul_comm, hbar]
    exact smul_right_injective _ hc0 h3
  have hadjy : adjM h y = h.bar a • (1 : Matrix (Fin 3) (Fin 3) K) + h.bar b • adjM h B +
      h.bar d • (adjM h B * adjM h B) := by
    rw [hyp, adjM_add, adjM_add, adjM_smul, adjM_smul, adjM_smul, adjM_one, adjM_mul]
  have hadjyv : adjM h y *ᵥ v = h.bar η • v := by
    rw [hadjy]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hadjBv, Matrix.mulVec_smul, smul_smul, hη, map_add, map_mul, map_pow]
    module
  have hN : η * h.bar η = 1 := by
    have h1 : v = (adjM h y * y) *ᵥ v := by rw [hy, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hyv, Matrix.mulVec_smul, hadjyv, smul_smul] at h1
    have h2 : (η * h.bar η - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv
  have hη9 : η ^ 9 = 1 := by
    rw [h.bar_apply] at hN
    rw [← hN, show (2 : ℕ) ^ 3 = 8 by norm_num]
    ring
  have hη2 : η ^ 2 = 1 := by
    calc η ^ 2 = η ^ 2 * η ^ 7 := by rw [hη7, mul_one]
      _ = η ^ 9 := by ring
      _ = 1 := hη9
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : (η - 1) ^ 2 = 0 := by linear_combination hη2 + (1 - η) * h2K
  have h5 := pow_eq_zero_iff (two_ne_zero) |>.mp h4
  exact sub_eq_zero.mp h5

theorem eq_one_of_regular {B y : Matrix (Fin 3) (Fin 3) K} {c : K} {u : Fin 3 → K}
    (hB : adjM h B * B = 1) (hB3 : B * B * B = c • (1 : Matrix (Fin 3) (Fin 3) K)) (hc3 : c ^ 3 = 1)
    (hu : (cycMat B u).det ≠ 0) (hy : adjM h y * y = 1) (hy7 : y ^ 7 = 1) (hyB : y * B = B * y) :
    y = 1 := by
  haveI := h.charP
  haveI := h.finite
  obtain ⟨a, b, d, hyp⟩ := exists_poly hu hyB
  have hK : Nat.card K = 64 := by rw [h.card]; norm_num
  have hc0 : c ≠ 0 := fun h0 => by rw [h0] at hc3; norm_num at hc3
  obtain ⟨l₀, hl₀9, hl₀3⟩ : ∃ l : K, l ^ 9 = 1 ∧ l ^ 3 = c := by
    have hδ : (Units.mk0 c hc0) ^ (2 + 1) = 1 := by
      apply Units.ext
      simpa using hc3
    obtain ⟨l, hl9, hl3⟩ := exists_cube_root_normOne (q₀ := 2) (K := K)
      (by rw [hK]; norm_num) (δ := Units.mk0 c hc0) hδ
    refine ⟨l, ?_, ?_⟩
    · have := congrArg Units.val hl9
      simpa using this
    · have := congrArg Units.val hl3
      simpa using this
  obtain ⟨ωu, hωo⟩ := exists_orderOf_eq_of_dvd_card (G := Kˣ) (d := 3)
    (by rw [Nat.card_units, hK]; norm_num)
  set ω : K := (ωu : K) with hω
  have hω3 : ω ^ 3 = 1 := by
    rw [hω, ← Units.val_pow_eq_pow_val, ← hωo, pow_orderOf_eq_one, Units.val_one]
  have hω1 : ω ≠ 1 := by
    intro h1
    have : ωu = 1 := Units.ext h1
    rw [this, orderOf_one] at hωo
    norm_num at hωo
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have h' : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hω1)
  have hl₀0 : l₀ ≠ 0 := by
    rintro rfl
    simp at hl₀9
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hroots : ∀ l : K, l ^ 9 = 1 → l ^ 3 = c → a + b * l + d * l ^ 2 = 1 := by
    intro l hl9 hl3
    obtain ⟨v, hv, hBv⟩ := exists_eigenvector_root hu hB3 hl3
    exact eigen_eta h hB hB3 hl9 hl3 hv hBv hyp hy hy7
  have h9 : ∀ k : ℕ, (ω ^ k * l₀) ^ 9 = 1 := by
    intro k
    rw [mul_pow, ← pow_mul, mul_comm k 9, pow_mul, show ω ^ 9 = 1 by
      rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hω3, one_pow], one_pow, one_mul, hl₀9]
  have h3 : ∀ k : ℕ, (ω ^ k * l₀) ^ 3 = c := by
    intro k
    rw [mul_pow, ← pow_mul, mul_comm k 3, pow_mul, hω3, one_pow, one_mul, hl₀3]
  have e0 := hroots l₀ hl₀9 hl₀3
  have e1 := hroots (ω ^ 1 * l₀) (h9 1) (h3 1)
  have e2 := hroots (ω ^ 2 * l₀) (h9 2) (h3 2)
  have hω4 : ω ^ 4 = ω := by linear_combination ω * hω3
  have h3K : (3 : K) = 1 := by linear_combination h2K
  have ha : a = 1 := by
    have h1 : (a - 1) * 3 = 0 := by
      linear_combination e0 + e1 + e2 - (b * l₀ + d * l₀ ^ 2) * hω2 - (d * l₀ ^ 2 * ω) * hω3
    rw [h3K, mul_one] at h1
    exact sub_eq_zero.mp h1
  subst ha
  have hd : d = 0 := by
    have h1 : d * l₀ ^ 2 * (1 - ω) = 0 := by
      linear_combination e0 - ω ^ 2 * e1 + (b * l₀ + d * l₀ ^ 2 * ω) * hω3
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact (hl₀0 ((pow_eq_zero_iff two_ne_zero).mp h3)).elim
    · exact absurd (sub_eq_zero.mp h2).symm hω1
  subst hd
  have hb : b = 0 := by
    have h1 : b * l₀ = 0 := by linear_combination e0
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hl₀0
  subst hb
  rw [hyp]
  simp

end Regular

variable {K : Type} [Field K]

theorem exists_mu (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (hσ : orderOf σ = 3) {ω : Kˣ}
    (hω : ω ^ 9 = 1) (hω3 : ω ^ 3 = 1) :
    ∃ μ : Kˣ, μ ^ 9 = 1 ∧ Units.map (σ : K →* K) μ = ω * μ := by
  have := h.finite
  obtain ⟨f₀, hf, -, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have hf₀ : f₀ = 1 := by omega
  subst hf₀
  have h₀ : UnitaryFieldData 2 1 (fixedField σ) := ⟨h.prime, le_refl 1, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  have hfix : ∀ c : Kˣ, c ^ (2 ^ 3 + 1) = 1 → σ c = c → c ^ (2 + 1) = 1 :=
    fun c hc hσc => pow_eq_one_of_fixed h h₀ hbar hc hσc
  have hK : Nat.card K = (2 ^ 3) ^ 2 := by
    rw [h.card]
    norm_num
  obtain ⟨μ, hμ, hσμ⟩ := exists_normOne_field_mul_eq (q₀ := 2) hK σ hfix hω hω3
  exact ⟨μ, hμ, hσμ⟩

theorem card_GF4_fintype : Fintype.card GF4 = 4 := by
  rfl

theorem exists_iota (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ ι : GF4 →+* K, (∀ a, σ (ι a) = ι a) ∧ (∀ y : K, σ y = y → ∃ a, ι a = y) := by
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have h1 : f₀ = 1 := by omega
  have hfin : Finite K := h.finite
  have : Fintype (fixedField σ) := Fintype.ofFinite _
  have hc4 : Nat.card (fixedField σ) = 4 := by simpa [h1] using hcard
  have hc4' : Fintype.card GF4 = Fintype.card (fixedField σ) := by
    rw [card_GF4_fintype, ← Nat.card_eq_fintype_card, hc4]
  have ρ : GF4 ≃+* fixedField σ := FiniteField.ringEquivOfCardEq hc4'
  refine ⟨(fixedField σ).subtype.comp ρ.toRingHom, ?_, ?_⟩
  · intro a
    exact CFSG.GH74.GLS.IVK.fixedField_apply σ (ρ a)
  · intro y hy
    have hmem : y ∈ fixedField σ := (CFSG.GH74.GLS.IVK.mem_fixedField_iff σ y).mpr hy
    refine ⟨ρ.symm ⟨y, hmem⟩, ?_⟩
    exact congrArg Subtype.val (ρ.apply_symm_apply ⟨y, hmem⟩)

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
