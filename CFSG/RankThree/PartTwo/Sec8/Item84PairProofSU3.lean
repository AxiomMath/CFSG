module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofPGL3
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeSU

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item84Pair

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {m : ℕ} {K : Type} [Field K]

theorem gram_entry {h : UnitaryFieldData 2 m K} {M G : Matrix (Fin 3) (Fin 3) K} {κ : K}
    (hM : (M.map h.bar)ᵀ * M = κ • 1) {d : Fin 3 → K} (hMG : M * G = G * diagonal d)
    (i k : Fin 3) :
    κ * ((G.map h.bar)ᵀ * G) i k = h.bar (d i) * d k * ((G.map h.bar)ᵀ * G) i k := by
  have e1 : ((M * G).map h.bar)ᵀ * (M * G) = κ • ((G.map h.bar)ᵀ * G) := by
    rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (M.map h.bar)ᵀ, hM, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have e2 : ((G * diagonal d).map h.bar)ᵀ * (G * diagonal d) =
      diagonal (fun i => h.bar (d i)) * ((G.map h.bar)ᵀ * G) * diagonal d := by
    rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.diagonal_map (map_zero _),
      Matrix.diagonal_transpose]
    simp only [Matrix.mul_assoc]
  rw [hMG] at e1
  have h1 := congrFun (congrFun (e1.symm.trans e2) i) k
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  rw [h1]
  ring

theorem det_gram_ne_zero (h : UnitaryFieldData 2 m K) {G : Matrix (Fin 3) (Fin 3) K}
    (hG : IsUnit G) : ((G.map h.bar)ᵀ * G).det ≠ 0 := by
  have hdet : G.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det G).mp hG |>.ne_zero
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact mul_ne_zero ((map_ne_zero h.bar).mpr hdet) hdet

theorem det_eq_zero_of_block {B : Matrix (Fin 3) (Fin 3) K} (h11 : B 1 1 = 0) (h12 : B 1 2 = 0)
    (h21 : B 2 1 = 0) (h22 : B 2 2 = 0) : B.det = 0 := by
  rw [Matrix.det_fin_three, h11, h12, h21, h22]
  ring

theorem det_eq_zero_of_row {B : Matrix (Fin 3) (Fin 3) K} (h00 : B 0 0 = 0) (h01 : B 0 1 = 0)
    (h02 : B 0 2 = 0) : B.det = 0 := by
  rw [Matrix.det_fin_three, h00, h01, h02]
  ring

theorem pow_eq_self_of_cube {x : K} (hx : x ^ 3 = 1) {q : ℕ} (hq : q % 3 = 1) : x ^ q = x := by
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 1 := ⟨q / 3, by omega⟩
  rw [hk, pow_succ, pow_mul, hx, one_pow, one_mul]

theorem false_of_even_matrix [Finite K] (h : UnitaryFieldData 2 m K) (hm : 2 ^ m % 3 = 1)
    {y S : Matrix (Fin 3) (Fin 3) K} (hyu : (y.map h.bar)ᵀ * y = 1) (hy3 : y ^ 3 = 1)
    (hys : ∀ c : K, y ≠ c • 1) {ν : K} (hS2 : S * S = ν • 1) (hSs : ∀ c : K, S ≠ c • 1)
    (hSy : S * y = y * S) : False := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hF : Sec4.PiField false 2 m K := ⟨Nat.prime_two, h.one_le, by
    rw [h.card, Sec4.piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [h.card]
    have hq : 2 ^ (2 * m) % 3 = 1 := by
      rw [pow_mul]
      norm_num [Nat.pow_mod]
    have : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
    omega
  obtain ⟨ω, hω⟩ := LangTwisted3Proof.exists_primitive_cube_root h3
  have hω3 : (ω : K) ^ 3 = 1 := LangTwisted3Proof.cube_eq_one_of_sq_add hω
  have hω1 : (ω : K) ≠ 1 := LangTwisted3Proof.ne_one_of_sq_add hω
  have h3K : (3 : K) ≠ 0 := by
    intro h3'
    have : (1 : K) = 0 := by linear_combination h3' - h2
    exact one_ne_zero this
  have hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x := fun x hx => by
    rw [UnitaryFieldData.bar_apply]
    exact pow_eq_self_of_cube hx hm
  obtain ⟨g, j, hg, hD⟩ := Sec4.exists_normal_form hω3 hω1 h3K hy3 hys
  set y' := (ω : K) ^ (j : ℕ) • y with hy'
  have hSy' : S * y' = y' * S := by
    rw [hy', Matrix.mul_smul, Matrix.smul_mul, hSy]
  have hωj3 : ((ω : K) ^ (j : ℕ)) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  set κ := h.bar ((ω : K) ^ (j : ℕ)) * (ω : K) ^ (j : ℕ) with hκ
  have hy'u : (y'.map h.bar)ᵀ * y' = κ • 1 := by
    rw [hy', Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, hyu, smul_smul]
  have hω2 : (ω : K) ^ 2 ≠ 1 := by
    intro h1
    apply hω1
    have h4 := hω3
    rw [pow_succ, h1, one_mul] at h4
    exact h4
  set B := (g.map h.bar)ᵀ * g with hB
  have hdet := det_gram_ne_zero h hg
  have key : ∀ ζ : K, ζ ^ 3 = 1 → ζ ≠ 1 → ζ ^ 2 ≠ 1 →
      y' * g = g * diagonal ![ζ, 1, 1] → False := by
    intro ζ hζ3 hζ1 hζ2 hyg
    have e := gram_entry hy'u hyg
    by_cases hκ1 : κ = 1
    · have hrow : ∀ k : Fin 3, k ≠ 0 → B 0 k = 0 := by
        intro k hk
        have hk' := e 0 k
        have hdk : (![ζ, 1, 1] : Fin 3 → K) k = 1 := by
          fin_cases k
          · exact absurd rfl hk
          · rfl
          · rfl
        rw [hκ1, one_mul, hdk, mul_one] at hk'
        change B 0 k = h.bar ζ * B 0 k at hk'
        rw [hbar ζ hζ3] at hk'
        have : (ζ - 1) * B 0 k = 0 := by linear_combination -hk'
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hζ1)
      have h00 : B 0 0 = 0 := by
        have hk' := e 0 0
        rw [hκ1, one_mul] at hk'
        change B 0 0 = h.bar ζ * ζ * B 0 0 at hk'
        rw [hbar ζ hζ3] at hk'
        have : (ζ ^ 2 - 1) * B 0 0 = 0 := by linear_combination -hk'
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hζ2)
      exact hdet (det_eq_zero_of_row h00 (hrow 1 (by decide)) (hrow 2 (by decide)))
    · have hblk : ∀ i k : Fin 3, i ≠ 0 → k ≠ 0 → B i k = 0 := by
        intro i k hi hk
        have hk' := e i k
        have hdi : (![ζ, 1, 1] : Fin 3 → K) i = 1 := by
          fin_cases i
          · exact absurd rfl hi
          · rfl
          · rfl
        have hdk : (![ζ, 1, 1] : Fin 3 → K) k = 1 := by
          fin_cases k
          · exact absurd rfl hk
          · rfl
          · rfl
        rw [hdi, hdk, map_one, one_mul, one_mul] at hk'
        have : (κ - 1) * B i k = 0 := by linear_combination hk'
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hκ1)
      exact hdet (det_eq_zero_of_block (hblk 1 1 (by decide) (by decide))
        (hblk 1 2 (by decide) (by decide)) (hblk 2 1 (by decide) (by decide))
        (hblk 2 2 (by decide) (by decide)))
  rcases hD with hD | hD | hD
  ·
    have hdist : ∀ i k : Fin 3, i ≠ k →
        (![(ω : K), (ω : K) ^ 2, 1] : Fin 3 → K) i ≠
          (![(ω : K), (ω : K) ^ 2, 1] : Fin 3 → K) k := by
      have hω0 : (ω : K) ≠ 0 := Units.ne_zero ω
      have h12 : (ω : K) ≠ (ω : K) ^ 2 := by
        intro h1
        apply hω1
        have : (ω : K) * ((ω : K) - 1) = 0 := by linear_combination -h1
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hω0)
      intro i k hik
      fin_cases i <;> fin_cases k
      all_goals first
        | exact absurd rfl hik
        | simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Fin.mk_one, Fin.zero_eta, Fin.isValue, Fin.reduceFinMk]
      all_goals first
        | exact h12 | exact h12.symm | exact hω1 | exact (Ne.symm hω1) | exact hω2
        | exact (Ne.symm hω2)
    obtain ⟨c, hc⟩ := LangTwisted3Proof.eq_smul_one_of_commute_diagonal hg hD hdist hSy' hS2
    exact hSs c hc
  · exact key ω hω3 hω1 hω2 hD
  · refine key ((ω : K) ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]) hω2 ?_ hD
    intro h1
    apply hω1
    have h4 : (ω : K) ^ 4 = 1 := by rw [← h1, ← pow_mul]
    calc (ω : K) = (ω : K) ^ 4 := by
          rw [show 4 = 3 + 1 by norm_num, pow_add, hω3, one_mul, pow_one]
      _ = 1 := h4

theorem exists_frame_unitary [Finite K] (h : UnitaryFieldData 2 m K) {A S : GL (Fin 3) K}
    (hA : A ∈ unitaryIsom3 h) (hA3 : A ^ 3 ∈ Subgroup.center (GL (Fin 3) K))
    (hAc : A ∉ Subgroup.center (GL (Fin 3) K)) (hS2 : S ^ 2 ∈ Subgroup.center (GL (Fin 3) K))
    (hSc : S ∉ Subgroup.center (GL (Fin 3) K))
    (hSA : ProjGenLinGroup.mk (S * A) = ProjGenLinGroup.mk (A * S)) :
    Odd m ∧ ∃ Q : GL (Fin 3) K, Q ∈ unitaryIsom3 h ∧ ∃ ζ : K, ζ ^ 2 + ζ + 1 = 0 ∧
      ∃ c : K, c ≠ 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) * Q = Q * diagonal ![c, c, c * ζ] := by
  have : CharP K 2 := h.charP
  have hF : Sec4.PiField false 2 m K := ⟨Nat.prime_two, h.one_le, by
    rw [h.card, Sec4.piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
  rcases Nat.even_or_odd m with hme | hmo
  · exfalso
    have hm : 2 ^ m % 3 = 1 := by
      obtain ⟨k, rfl⟩ := hme
      rw [← two_mul, pow_mul]
      norm_num [Nat.pow_mod]
    have hA3u : A ^ 3 ∈ unitaryIsom3 h := pow_mem hA 3
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA3 hS2 hAc hSc
    obtain ⟨τ, hτ⟩ := hA3
    obtain ⟨ν, hν⟩ := hS2
    set Am := (A : Matrix (Fin 3) (Fin 3) K) with hAm
    set Sm := (S : Matrix (Fin 3) (Fin 3) K) with hSm
    have hscal : ∀ c : Kˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = (c : K) • 1 := fun c => by
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hAm3 : Am ^ 3 = (τ : K) • 1 := by
      rw [hAm, ← Units.val_pow_eq_pow_val, ← hτ, hscal]
    have hSm2 : Sm * Sm = (ν : K) • 1 := by
      rw [hSm, ← Units.val_mul, ← sq, ← hν, hscal]
    have hnotscal : ∀ (g : GL (Fin 3) K),
        g ∉ Set.range (Matrix.GeneralLinearGroup.scalar (Fin 3)) →
        ∀ c : K, (g : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
      intro g hg c hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        exact not_isUnit_zero (hc ▸ g.isUnit)
      exact hg ⟨Units.mk0 c hc0, Units.ext (by rw [hscal, Units.val_mk0, hc])⟩
    have hAs := hnotscal A hAc
    have hSs := hnotscal S hSc
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 hSA
    have hSAm : Sm * Am = ((u⁻¹ : Kˣ) : K) • (Am * Sm) := by
      have e := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hu
      simp only [Units.val_mul, hscal] at e
      rw [← e, Matrix.mul_smul, Matrix.mul_one, smul_smul, Units.val_inv_eq_inv_val,
        inv_mul_cancel₀ (Units.ne_zero u), one_smul]
    have hcomm : Sm * Am = Am * Sm :=
      LangTwisted3Proof.commute_of_mul_eq_smul (Units.ne_zero ν) A.isUnit hSm2 hSAm
    have hτq : h.bar (τ : K) * τ = 1 := by
      rw [← hτ, mem_unitaryIsom3, hscal] at hA3u
      have e := congrFun (congrFun hA3u 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using e
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ m = 3 * t + 1 := ⟨2 ^ m / 3, by omega⟩
    set η : Kˣ := τ ^ (t + 1) with hη
    have hτq' : (τ : K) ^ (2 ^ m + 1) = 1 := by
      rw [pow_succ, ← UnitaryFieldData.bar_apply]
      exact hτq
    have hη3 : (η : K) ^ 3 = τ := by
      rw [hη, Units.val_pow_eq_pow_val, ← pow_mul,
        show (t + 1) * 3 = (2 ^ m + 1) + 1 by omega, pow_succ, hτq', one_mul]
    have hηq : h.bar (η : K) * η = 1 := by
      rw [UnitaryFieldData.bar_apply, ← pow_succ, hη, Units.val_pow_eq_pow_val, ← pow_mul,
        mul_comm, pow_mul, hτq', one_pow]
    have hη0 : (η : K) ≠ 0 := Units.ne_zero η
    set y := (η : K)⁻¹ • Am with hy
    have hAu : (Am.map h.bar)ᵀ * Am = 1 := hA
    have hyu : (y.map h.bar)ᵀ * y = 1 := by
      rw [hy, Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.transpose_smul, Matrix.smul_mul,
        Matrix.mul_smul, hAu, smul_smul, map_inv₀, ← mul_inv, hηq, inv_one, one_smul]
    have hy3 : y ^ 3 = 1 := by
      rw [hy, smul_pow, hAm3, smul_smul, inv_pow, hη3, inv_mul_cancel₀ (Units.ne_zero τ),
        one_smul]
    have hys : ∀ c : K, y ≠ c • 1 := by
      intro c hc
      apply hAs ((η : K) * c)
      calc Am = (η : K) • y := by rw [hy, smul_smul, mul_inv_cancel₀ hη0, one_smul]
        _ = ((η : K) * c) • 1 := by rw [hc, smul_smul]
    have hSy : Sm * y = y * Sm := by
      rw [hy, Matrix.mul_smul, Matrix.smul_mul, hcomm]
    exact false_of_even_matrix h hm hyu hy3 hys hSm2 hSs hSy
  · have hmod : Sec4.ModThree false (2 ^ m) := by
      obtain ⟨k, rfl⟩ := hmo
      show 2 ^ (2 * k + 1) % 3 = 2
      rw [pow_succ, pow_mul]
      norm_num [Nat.mul_mod, Nat.pow_mod]
    obtain ⟨ω, hω⟩ := LangTwisted3Proof.exists_primitive_cube_root
      (LangTwisted3Proof.three_dvd_card_sub_one hF hmod)
    have hg : A ∈ Sec4.glPi false 3 (2 ^ m) K := (Sec4.mem_glPi_false h).2 hA
    obtain ⟨Q, hQ, ζ, hζ, c, hc0, hAQ⟩ :=
      LangTwisted3Proof.exists_frame hF hmod hω hg hA3 hAc hS2 hSc hSA
    refine ⟨hmo, Q, (Sec4.mem_glPi_false h).1 hQ, ζ, ?_, c, hc0, hAQ⟩
    have hω3 := LangTwisted3Proof.cube_eq_one_of_sq_add hω
    rcases hζ with rfl | rfl
    · exact hω
    · linear_combination (ω : K) * hω3 + hω

theorem pow_three_mem_center {h : UnitaryFieldData 2 m K} {A : unitaryIsom3 h}
    (hA3 : psuConj h A ^ 3 = 1) :
    (A : GL (Fin 3) K) ^ 3 ∈ Subgroup.center (GL (Fin 3) K) := by
  have h1 : psuConj h (A ^ 3) * psuField h 1 = 1 := by rw [map_one, mul_one, map_pow, hA3]
  obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, by rw [← hc, Subgroup.coe_pow]⟩

theorem not_mem_center_of_psuConj_ne_one {h : UnitaryFieldData 2 m K} {A : unitaryIsom3 h}
    (hA1 : psuConj h A ≠ 1) : (A : GL (Fin 3) K) ∉ Subgroup.center (GL (Fin 3) K) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  rintro ⟨c, hc⟩
  apply hA1
  have hcA : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h := hc ▸ A.2
  have hA : A = ⟨_, hcA⟩ := Subtype.ext hc.symm
  rw [hA]
  exact psuConj_scalar hcA

@[expose] noncomputable def dZeta {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) : GL (Fin 3) K :=
  LangTwisted3Proof.dOmega (Units.mk0 ζ (by
    rintro rfl
    have : (1 : K) = 0 := by linear_combination hζ
    exact one_ne_zero this))

theorem coe_dZeta {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    ((dZeta hζ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, 1, ζ] :=
  LangTwisted3Proof.coe_dOmega _

theorem one_ne_of_sq_add [CharP K 2] {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) : (1 : K) ≠ ζ :=
  fun h1 => LangTwisted3Proof.ne_one_of_sq_add hζ h1.symm

theorem eq_scalar_mul_conj {A Q : GL (Fin 3) K} {ζ c : K} (hζ : ζ ^ 2 + ζ + 1 = 0) (hc0 : c ≠ 0)
    (hAQ : (A : Matrix (Fin 3) (Fin 3) K) * Q = Q * diagonal ![c, c, c * ζ]) :
    A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * (Q * dZeta hζ * Q⁻¹) := by
  apply Units.ext
  have hd : diagonal ![c, c, c * ζ] = c • diagonal ![1, 1, ζ] := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    fin_cases i <;> simp
  have h1 : (A : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * Q * ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, coe_dZeta, h1, hAQ, hd, Units.val_mk0, ← Matrix.smul_eq_diagonal_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem commute_conj_iff {A Q D x : GL (Fin 3) K} {c : Kˣ}
    (hA : A = GeneralLinearGroup.scalar (Fin 3) c * (Q * D * Q⁻¹)) :
    x * A = A * x ↔ (Q⁻¹ * x * Q) * D = D * (Q⁻¹ * x * Q) := by
  have hs : x * GeneralLinearGroup.scalar (Fin 3) c = GeneralLinearGroup.scalar (Fin 3) c * x :=
    (commute_scalar c x).eq
  have ea : x * A = GeneralLinearGroup.scalar (Fin 3) c * (x * (Q * D * Q⁻¹)) := by
    rw [hA, ← mul_assoc, hs, mul_assoc]
  have eb : A * x = GeneralLinearGroup.scalar (Fin 3) c * ((Q * D * Q⁻¹) * x) := by
    rw [hA, mul_assoc]
  have e0 : x * A = A * x ↔ x * (Q * D * Q⁻¹) = (Q * D * Q⁻¹) * x := by
    rw [ea, eb, mul_right_inj]
  have e1 : (Q⁻¹ * x * Q) * D = Q⁻¹ * (x * (Q * D * Q⁻¹)) * Q := by group
  have e2 : D * (Q⁻¹ * x * Q) = Q⁻¹ * ((Q * D * Q⁻¹) * x) * Q := by group
  rw [e0, e1, e2, mul_left_inj, mul_right_inj]

theorem suCentralizer_eq_map {h : UnitaryFieldData 2 m K} {A D : GL (Fin 3) K}
    (Q : unitaryIsom3 h) {c : Kˣ}
    (hA : A = GeneralLinearGroup.scalar (Fin 3) c *
      ((Q : GL (Fin 3) K) * D * (Q⁻¹ : GL (Fin 3) K))) :
    suCentralizer (2 ^ m) A = (suCentralizer (2 ^ m) D).map (suConj h Q).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_suCentralizer, mem_suCentralizer, ← MulAut.inv_def,
    ← map_inv, coe_suConj, Subgroup.coe_inv, inv_inv, commute_conj_iff hA]

theorem kf_su3_fix [Finite K] (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m) (A : unitaryIsom3 h)
    (hA1 : suConj h A ≠ 1) (hA3 : suConj h A ^ 3 = 1)
    (hinv : ∃ x ∈ suCentralizer (2 ^ m) (A : GL (Fin 3) K), x ≠ 1 ∧ x ^ 2 = 1) :
    Odd m ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = 2 ^ m ∧
      Nonempty (inSubgroup perfectResidual (suCentralizer (2 ^ m) (A : GL (Fin 3) K)) ≃*
        SL(2, F₀)) := by
  have : CharP K 2 := h.charP
  have hq4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq : 2 < 2 ^ m := by omega
  have hP3 : psuConj h A ^ 3 = 1 := by
    rw [← OutFixCentralThree.congr_centerDescend_suConj hq A, ← map_pow, ← map_pow, hA3, map_one,
      map_one]
  have hA3c := pow_three_mem_center hP3
  have hAc : (A : GL (Fin 3) K) ∉ Subgroup.center (GL (Fin 3) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rintro ⟨c, hc⟩
    apply hA1
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [coe_suConj, Subgroup.coe_inv, ← hc, ← (commute_scalar c (g : GL (Fin 3) K)).eq,
      mul_inv_cancel_right]
    rfl
  obtain ⟨x, hx, hx1, hx2⟩ := hinv
  have hxA : (x : GL (Fin 3) K) * A = A * x := mem_suCentralizer.mp hx
  have hxc : (x : GL (Fin 3) K) ∉ Subgroup.center (GL (Fin 3) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rintro ⟨c, hc⟩
    apply hx1
    have h2 : (GeneralLinearGroup.scalar (Fin 3) c) ^ 2 = 1 := by
      rw [hc, ← Subgroup.coe_pow, hx2, Subgroup.coe_one]
    have hc2 : (c : K) ^ 2 = 1 := by
      rw [← map_pow] at h2
      have h3 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h2
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_one,
        Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h3
      rw [← Units.val_pow_eq_pow_val]
      exact h3
    have hc1 : (c : K) = 1 := LangTwisted3Proof.eq_of_sq_eq_sq_of_charTwo (by rw [hc2, one_pow])
    have : c = 1 := Units.ext hc1
    apply Subtype.ext
    rw [← hc, this, map_one]
    rfl
  have hx2c : (x : GL (Fin 3) K) ^ 2 ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← Subgroup.coe_pow, hx2]
    exact one_mem _
  have hxA' : ProjGenLinGroup.mk ((x : GL (Fin 3) K) * (A : GL (Fin 3) K)) =
      ProjGenLinGroup.mk ((A : GL (Fin 3) K) * (x : GL (Fin 3) K)) := by rw [hxA]
  obtain ⟨hmo, Q, hQ, ζ, hζ, c, hc0, hAQ⟩ :=
    exists_frame_unitary h A.2 hA3c hAc hx2c hxc hxA'
  have hAeq := eq_scalar_mul_conj hζ hc0 hAQ
  have hmap := suCentralizer_eq_map (h := h) ⟨Q, hQ⟩ (D := dZeta hζ) hAeq
  obtain ⟨F₀, hF₀, hF₀', hcard, ⟨ι⟩⟩ := exists_perfectResidual_suCentralizer_mulEquiv h hq4
    (one_ne_of_sq_add hζ) (coe_dZeta hζ)
  refine ⟨hmo, F₀, hF₀, hF₀', hcard, ⟨?_⟩⟩
  have heq : inSubgroup perfectResidual (suCentralizer (2 ^ m) (A : GL (Fin 3) K)) =
      (inSubgroup perfectResidual (suCentralizer (2 ^ m) (dZeta hζ))).map
        (suConj h ⟨Q, hQ⟩).toMonoidHom := by
    rw [hmap, map_inSubgroup_perfectResidual]
  exact (MulEquiv.subgroupCongr heq).trans
    ((Subgroup.equivMapOfInjective _ _ (suConj h ⟨Q, hQ⟩).injective).symm.trans ι)

theorem dZeta_mem (h : UnitaryFieldData 2 m K) (hm : Odd m) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    dZeta hζ ∈ unitaryIsom3 h := by
  have hF : Sec4.PiField false 2 m K := ⟨Nat.prime_two, h.one_le, by
    rw [h.card, Sec4.piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
  have hmod : Sec4.ModThree false (2 ^ m) := by
    obtain ⟨k, rfl⟩ := hm
    show 2 ^ (2 * k + 1) % 3 = 2
    rw [pow_succ, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have hmem := LangTwisted3Proof.dOmega_mem hF hmod
    (ζ := Units.mk0 ζ (by
      rintro rfl
      have : (1 : K) = 0 := by linear_combination hζ
      exact one_ne_zero this)) (LangTwisted3Proof.cube_eq_one_of_sq_add hζ)
  exact (Sec4.mem_glPi_false h).1 hmem

theorem kf_psu3_fix [Finite K] (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m) (A : unitaryIsom3 h)
    (hA1 : psuConj h A ≠ 1) (hA3 : psuConj h A ^ 3 = 1) (S : Subgroup (unitaryPSU h 3))
    (hS : ∀ z, z ∈ S ↔ psuConj h A z = z) (hinv : ∃ z ∈ S, z ≠ 1 ∧ z ^ 2 = 1) :
    Odd m ∧ ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = 2 ^ m ∧
      Nonempty (inSubgroup perfectResidual S ≃* SL(2, F₀)) := by
  have : CharP K 2 := h.charP
  have hq4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hA3c := pow_three_mem_center hA3
  have hAc := not_mem_center_of_psuConj_ne_one hA1
  obtain ⟨z, hzS, hz1, hz2⟩ := hinv
  obtain ⟨x, rfl⟩ := unitaryProj_surjective h 3 z
  have hfix : psuConj h A (unitaryProj h 3 x) = unitaryProj h 3 x := (hS _).mp hzS
  rw [unitaryProj, QuotientGroup.mk'_apply, psuConj_mk, QuotientGroup.eq] at hfix
  obtain ⟨c, -, -, hc⟩ := hfix
  have h1 : ((A : GL (Fin 3) K) * x * (A : GL (Fin 3) K)⁻¹)⁻¹ * (x : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, coe_suConj, Subgroup.coe_inv]
  have h2 := inv_mul_eq_iff_eq_mul.mp h1
  have h3 : (x : GL (Fin 3) K) * A =
      (A : GL (Fin 3) K) * x * GeneralLinearGroup.scalar (Fin 3) c := by
    have hcomm := (commute_scalar c (A : GL (Fin 3) K)).eq
    conv_lhs => rw [h2]
    rw [mul_assoc _ (GeneralLinearGroup.scalar (Fin 3) c), ← hcomm]
    group
  have hxA : ProjGenLinGroup.mk ((x : GL (Fin 3) K) * (A : GL (Fin 3) K)) =
      ProjGenLinGroup.mk ((A : GL (Fin 3) K) * (x : GL (Fin 3) K)) := by
    rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨c⁻¹, ?_⟩
    rw [h3, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have hx2 : (x : GL (Fin 3) K) ^ 2 ∈ Subgroup.center (GL (Fin 3) K) := by
    have h4 : unitaryProj h 3 (x ^ 2) = 1 := by rw [map_pow]; exact hz2
    rw [← MonoidHom.mem_ker, ker_unitaryProj] at h4
    obtain ⟨d, -, -, hd⟩ := h4
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨d, by rw [← hd, Subgroup.coe_pow]⟩
  have hxc : (x : GL (Fin 3) K) ∉ Subgroup.center (GL (Fin 3) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rintro ⟨d, hd⟩
    apply hz1
    rw [← MonoidHom.mem_ker, ker_unitaryProj, unitaryScalars_eq h (by norm_num),
      Subgroup.mem_subgroupOf]
    exact ⟨d, hd⟩
  obtain ⟨hmo, Q, hQ, ζ, hζ, c', hc0, hAQ⟩ :=
    exists_frame_unitary h A.2 hA3c hAc hx2 hxc hxA
  have hAeq := eq_scalar_mul_conj hζ hc0 hAQ
  have hD := dZeta_mem h hmo hζ
  set Q' : unitaryIsom3 h := ⟨Q, hQ⟩ with hQ'
  set D' : unitaryIsom3 h := ⟨dZeta hζ, hD⟩ with hD'
  have hsc : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c' hc0) ∈ unitaryIsom3 h := by
    have e : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c' hc0) =
        (A : GL (Fin 3) K) * ((Q : GL (Fin 3) K) * dZeta hζ * Q⁻¹)⁻¹ := by
      rw [hAeq, mul_inv_cancel_right]
    rw [e]
    exact mul_mem A.2 (inv_mem (mul_mem (mul_mem hQ hD) (inv_mem hQ)))
  have hAQD : A = ⟨_, hsc⟩ * (Q' * D' * Q'⁻¹) := Subtype.ext hAeq
  have hconj : psuConj h A = psuConj h Q' * psuConj h D' * (psuConj h Q')⁻¹ := by
    rw [hAQD, map_mul, psuConj_scalar hsc, one_mul, map_mul, map_mul, map_inv]
  set T := (suCentralizer (2 ^ m) (D' : GL (Fin 3) K)).map (unitaryProj h 3) with hT
  have hST : S = T.map (psuConj h Q').toMonoidHom := by
    ext w
    rw [Subgroup.mem_map_equiv, ← MulAut.inv_def, hT, mem_map_suCentralizer_iff h (coe_dZeta hζ),
      hS, hconj]
    constructor
    · intro hw
      have := congrArg (fun v => (psuConj h Q')⁻¹ v) hw
      simpa [MulAut.mul_apply] using this
    · intro hw
      have := congrArg (fun v => psuConj h Q' v) hw
      simpa [MulAut.mul_apply] using this
  obtain ⟨F₀, hF₀, hF₀', hcard, ⟨ι⟩⟩ := exists_perfectResidual_psuFixed_mulEquiv h hq4
    (one_ne_of_sq_add hζ) (A := D') (coe_dZeta hζ)
  refine ⟨hmo, F₀, hF₀, hF₀', hcard, ⟨?_⟩⟩
  have heq : inSubgroup perfectResidual S =
      (inSubgroup perfectResidual T).map (psuConj h Q').toMonoidHom := by
    rw [hST, map_inSubgroup_perfectResidual]
  exact (MulEquiv.subgroupCongr heq).trans
    ((Subgroup.equivMapOfInjective _ _ (psuConj h Q').injective).symm.trans ι)

end CFSG.RankThree.PartTwo.Sec8.Item84Pair
