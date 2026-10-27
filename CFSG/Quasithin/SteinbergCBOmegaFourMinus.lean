module

public import CFSG.Quasithin.SteinbergCBTwistedIsometry
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.SteinbergCB

open Matrix
open scoped TensorProduct commutatorElement

theorem twistRep_injective {F : Type*} [Field F] {σ : F →+* F} (h2 : (2 : F) = 0)
    (hinv : ∀ x, σ (σ x) = x) : Function.Injective (twistRep hinv) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hX : ∀ X : twistedForm σ, (g : Matrix (Fin 2) (Fin 2) F) * X *
      ((g : Matrix (Fin 2) (Fin 2) F).map σ)ᵀ = X := fun X => by
    rw [← twistRep_apply hinv, hg]
    rfl
  have he := hX (twMk hinv 1 0 0)
  have hf := hX (twMk hinv 0 0 1)
  have hy := hX (twMk hinv 0 1 0)
  rw [twMk_coe] at he hf hy
  have hent : ∀ (M : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2),
      ((g : Matrix (Fin 2) (Fin 2) F) * M * ((g : Matrix (Fin 2) (Fin 2) F).map σ)ᵀ) i j =
        (g : Matrix (Fin 2) (Fin 2) F) i 0 * (M 0 0 * σ ((g : Matrix (Fin 2) (Fin 2) F) j 0) +
          M 0 1 * σ ((g : Matrix (Fin 2) (Fin 2) F) j 1)) +
        (g : Matrix (Fin 2) (Fin 2) F) i 1 * (M 1 0 * σ ((g : Matrix (Fin 2) (Fin 2) F) j 0) +
          M 1 1 * σ ((g : Matrix (Fin 2) (Fin 2) F) j 1)) := by
    intro M i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply]
    ring
  have hs : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h := congrFun (congrFun he 1) 1
    rw [hent] at h
    simpa using h
  have hr : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h := congrFun (congrFun hf 0) 0
    rw [hent] at h
    simpa using h
  have f11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 * σ ((g : Matrix (Fin 2) (Fin 2) F) 1 1) = 1 := by
    have h := congrFun (congrFun hf 1) 1
    rw [hent] at h
    simpa using h
  have y01 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * σ ((g : Matrix (Fin 2) (Fin 2) F) 1 1) = 1 := by
    have h := congrFun (congrFun hy 0) 1
    rw [hent, hr] at h
    simpa using h
  have hdet := g.2
  rw [det_fin_two, hs, hr, mul_zero, sub_zero] at hdet
  have hp : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hσt : σ ((g : Matrix (Fin 2) (Fin 2) F) 1 1) = (g : Matrix (Fin 2) (Fin 2) F) 1 1 :=
    mul_left_cancel₀ hp (y01.trans hdet.symm)
  rw [hσt] at f11
  have ht : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have hsq : ((g : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) ^ 2 = 0 := by
      linear_combination f11 + (1 - (g : Matrix (Fin 2) (Fin 2) F) 1 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  rw [ht, mul_one] at hdet
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hdet, hr, hs, ht]

theorem exists_frob_ringHom {F : Type*} [Field F] [Finite F] {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = (2 ^ m) ^ 2) : ∃ σ : F →+* F, ∀ x, σ x = x ^ 2 ^ m := by
  have : CharP F 2 := charP_two_of_card hm hF
  have : ExpChar F 2 := ExpChar.prime Nat.prime_two
  exact ⟨iterateFrobenius F 2 m, fun x => iterateFrobenius_def (p := 2) m x⟩

theorem SL2_q0sq_Omega4minus_twisted_tensor {F : Type*} [Field F] [Finite F] (m : ℕ)
    (hm : 1 ≤ m) (hF : Nat.card F = (2 ^ m) ^ 2) (σ : F →+* F) (hσ : ∀ x, σ x = x ^ 2 ^ m) :
    Nat.card (frobFixed σ) = 2 ^ m ∧
    (∀ g : Matrix.SpecialLinearGroup (Fin 2) F, ∀ X ∈ twistedForm σ,
      (g : Matrix (Fin 2) (Fin 2) F) * X * ((g : Matrix (Fin 2) (Fin 2) F).map σ)ᵀ ∈
        twistedForm σ) ∧
    Module.finrank (frobFixed σ) (twistedForm σ) = 4 ∧
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 2) F →* (twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ),
      (∀ g X, ((ρ g X : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) =
        (g : Matrix (Fin 2) (Fin 2) F) * X * ((g : Matrix (Fin 2) (Fin 2) F).map σ)ᵀ) ∧
      Function.Bijective ((twistedForm σ).subtype.liftBaseChange F) ∧
      (∀ g t, (twistedForm σ).subtype.liftBaseChange F
          (LinearMap.baseChange F (ρ g).toLinearMap t) =
        (g : Matrix (Fin 2) (Fin 2) F) * (twistedForm σ).subtype.liftBaseChange F t *
          ((g : Matrix (Fin 2) (Fin 2) F).map σ)ᵀ) ∧
      ∃ Q : QuadraticForm (frobFixed σ) (twistedForm σ),
        (∀ X, (Q X : F) = (X : Matrix (Fin 2) (Fin 2) F).det) ∧
        (∀ X, (∀ Y, QuadraticMap.polar Q X Y = 0) → X = 0) ∧
        (∃ e f : twistedForm σ, Q e = 0 ∧ Q f = 0 ∧ QuadraticMap.polar Q e f = 1 ∧
          ∃ A : Submodule (frobFixed σ) (twistedForm σ),
            IsCompl (Submodule.span (frobFixed σ) {e, f}) A ∧
            (∀ a ∈ A, QuadraticMap.polar Q e a = 0 ∧ QuadraticMap.polar Q f a = 0) ∧
            Module.finrank (frobFixed σ) A = 2 ∧ ∀ a ∈ A, Q a = 0 → a = 0) ∧
        (∀ U : Submodule (frobFixed σ) (twistedForm σ), (∀ u ∈ U, Q u = 0) →
          Module.finrank (frobFixed σ) U ≤ 1) ∧
        (∃ U : Submodule (frobFixed σ) (twistedForm σ), (∀ u ∈ U, Q u = 0) ∧
          Module.finrank (frobFixed σ) U = 1) ∧
        (∀ g X, Q (ρ g X) = Q X) ∧
        Function.Injective ρ ∧
        ρ.range = ⁅isometryGroup Q, isometryGroup Q⁆ ∧
        Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃*
          (⁅isometryGroup Q, isometryGroup Q⁆ : Subgroup _)) ∧
        Nat.card (⁅isometryGroup Q, isometryGroup Q⁆ : Subgroup _) =
          (2 ^ m) ^ 2 * ((2 ^ m) ^ 4 - 1) := by
  have h2 := two_eq_zero_of_card hm hF
  have hinv := frob_frob hF hσ
  obtain ⟨ω, hω⟩ := exists_frob_ne hm hF hσ
  have hF0 := card_frobFixed hm hF hσ
  have hinj := twistRep_injective h2 hinv
  have hQe : twistedDet σ (twMk hinv 1 0 0) = 0 := by
    apply Subtype.ext
    rw [twistedDet_apply, twMk_coe, det_fin_two_of]
    simp
  have hQf : twistedDet σ (twMk hinv 0 0 1) = 0 := by
    apply Subtype.ext
    rw [twistedDet_apply, twMk_coe, det_fin_two_of]
    simp
  have he0 : twMk hinv 1 0 0 ≠ 0 := by
    intro h0
    have := congrArg (fun X : twistedForm σ => (X : Matrix (Fin 2) (Fin 2) F) 0 0) h0
    simp [twMk_coe] at this
  have hK : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      (2 ^ m) ^ 2 * (((2 ^ m) ^ 2) ^ 2 - 1) := by
    rw [CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup, hF]
  set O := isometryGroup (twistedDet σ) with hO
  set P := (twistRep hinv).range with hP
  have hle : P ≤ O := by
    rintro _ ⟨g, rfl⟩
    exact fun X => twistedDet_twistRep hinv g X
  have hcardP : Nat.card P = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hObound : Nat.card O ≤ 2 * Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    have hb := card_isometryGroup_le hinv hω
    have hN := card_frob_norm_one_le (m := m) hσ
    rw [hF0, hF] at hb
    rw [hK]
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h4 : 1 ≤ ((2 ^ m) ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    calc Nat.card O ≤ ((2 ^ m - 1) * (2 ^ m) ^ 2 + (2 ^ m - 1)) *
          ((2 ^ m) ^ 2 * (2 * (2 ^ m + 1))) := hb.trans (by gcongr)
      _ = 2 * ((2 ^ m) ^ 2 * (((2 ^ m) ^ 2) ^ 2 - 1)) := by
        zify [h1, h4]
        ring
  have : Finite (twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ) :=
    Finite.of_injective (fun e => (e : twistedForm σ → twistedForm σ)) DFunLike.coe_injective
  have hidx := Subgroup.card_mul_index (P.subgroupOf O)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardP] at hidx
  have hKpos : 0 < Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := Nat.card_pos
  have hidx0 : (P.subgroupOf O).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx2 : (P.subgroupOf O).index ≤ 2 := by
    by_contra h
    push Not at h
    have h3 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * 3 ≤
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * (P.subgroupOf O).index :=
      Nat.mul_le_mul_left _ h
    omega
  have hcomm : ⁅O, O⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have key : ⁅(⟨a, ha⟩ : O), (⟨b, hb⟩ : O)⁆ ∈ P.subgroupOf O := by
      rcases (by omega : (P.subgroupOf O).index = 1 ∨ (P.subgroupOf O).index = 2) with h | h
      · rw [Subgroup.index_eq_one] at h
        rw [h]
        exact Subgroup.mem_top _
      · rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h,
          Subgroup.mul_mem_iff_of_index_two h, Subgroup.mul_mem_iff_of_index_two h,
          inv_mem_iff, inv_mem_iff]
        tauto
    exact (Subgroup.mem_subgroupOf).1 key
  have hperf : P ≤ ⁅O, O⁆ := by
    have hK4 : 4 ≤ Nat.card F := by
      rw [hF]
      have : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      nlinarith
    have hperfK := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hK4
    rw [hP, MonoidHom.range_eq_map, ← hperfK.commutator_eq_top, commutator_def,
      Subgroup.map_commutator]
    have hmap : Subgroup.map (twistRep hinv) ⊤ ≤ O := by
      rw [← MonoidHom.range_eq_map]
      exact hle
    exact Subgroup.commutator_mono hmap hmap
  have hrange : P = ⁅O, O⁆ := le_antisymm hperf hcomm
  refine ⟨hF0, fun g X hX => twist_mem hinv _ hX, finrank_twistedForm hinv hω, twistRep hinv,
    fun g X => twistRep_apply hinv g X, liftBaseChange_twistedForm_bijective hinv hω,
    liftBaseChange_twistRep hinv, twistedDet σ, twistedDet_apply,
    twistedDet_polar_nondegenerate h2 hinv hω, ?_, finrank_le_one_of_totally_singular, ?_,
    twistedDet_twistRep hinv, hinj, hrange,
    ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩, ?_⟩
  · refine ⟨twMk hinv 1 0 0, twMk hinv 0 0 1, hQe, hQf, ?_, LinearMap.ker (twistDiag σ),
      isCompl_span_ker_twistDiag hinv, fun a ha => polar_twMk_of_mem_ker hinv ha,
      finrank_ker_twistDiag hinv hω, fun a ha hQ => eq_zero_of_mem_ker_twistDiag ha hQ⟩
    apply Subtype.ext
    rw [twistedDet_polar_twMk, twMk_coe]
    simp
  · refine ⟨Submodule.span (frobFixed σ) {twMk hinv 1 0 0}, fun u hu => ?_,
      finrank_span_singleton he0⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [QuadraticMap.map_smul, hQe, smul_zero]
  · rw [← hrange, hcardP, hK, show ((2 ^ m) ^ 2) ^ 2 = (2 ^ m) ^ 4 by ring]
