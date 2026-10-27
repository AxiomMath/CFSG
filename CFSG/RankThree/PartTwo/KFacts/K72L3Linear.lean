module

public import CFSG.RankThree.PartTwo.KFacts.K72L3Group
public import CFSG.GH74.GLS.IVK.L2.Fixed
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.RankThree.PartTwo.KFacts.AutKinds

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

section Linear

variable {K : Type} [Field K]

theorem units_eq_one_of_pow_three_eq_one (hK : Nat.card K % 3 = 2) {c : Kˣ} (hc : c ^ 3 = 1) :
    c = 1 := by
  have h1 : c ^ (Nat.card K - 1) = 1 := by rw [← Nat.card_units]; exact pow_card_eq_one'
  have hg : Nat.gcd 3 (Nat.card K - 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  have h := pow_gcd_eq_one.mpr ⟨hc, h1⟩
  rwa [hg, pow_one] at h

theorem scalars_three_eq_bot_of_mod_three (hK : Nat.card K % 3 = 2) : scalars 3 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  rw [Subgroup.mem_bot]
  obtain rfl := units_eq_one_of_pow_three_eq_one hK hc
  ext i j
  simp [hA]

theorem proj_three_injective (hK : Nat.card K % 3 = 2) : Function.Injective (proj 3 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_three_eq_bot_of_mod_three hK]

theorem isInnerAut_of_mem_linearAutGroup (hK : Nat.card K % 3 = 2)
    {β : MulAut (projectiveSL 3 K)} (hβ : β ∈ linearAutGroup 3 K) : IsInnerAut β := by
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hβ
  have hcop : (Nat.card Kˣ).Coprime 3 := by
    rw [Nat.card_units, Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  set u : Kˣ := (powCoprime hcop).symm (GeneralLinearGroup.det A) with hu
  have hu3 : u ^ 3 = GeneralLinearGroup.det A := by
    rw [← powCoprime_apply hcop, hu, Equiv.apply_symm_apply]
  exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_range_conj_of_det_eq_pow hu3.symm

theorem map_eq_of_fieldAut_proj_eq (hK : Nat.card K % 3 = 2) (σ : K ≃+* K)
    {A : SpecialLinearGroup (Fin 3) K} (h : fieldAut 3 K σ (proj 3 K A) = proj 3 K A) :
    SpecialLinearGroup.map σ.toRingHom A = A := by
  rw [fieldAut_proj] at h
  exact proj_three_injective hK h

theorem exists_sl_map_subtype_eq {σ : K ≃+* K} {A : SpecialLinearGroup (Fin 3) K}
    (hA : SpecialLinearGroup.map σ.toRingHom A = A) :
    ∃ A₀ : SpecialLinearGroup (Fin 3) (GH74.GLS.IVK.fixedField σ),
      SpecialLinearGroup.map (GH74.GLS.IVK.fixedField σ).subtype A₀ = A := by
  set K₀ := GH74.GLS.IVK.fixedField σ
  have hfix : ∀ i j, σ ((A : Matrix (Fin 3) (Fin 3) K) i j) =
      (A : Matrix (Fin 3) (Fin 3) K) i j :=
    fun i j => congrFun (congrFun (congrArg (fun B : SpecialLinearGroup (Fin 3) K =>
      (B : Matrix (Fin 3) (Fin 3) K)) hA) i) j
  set M : Matrix (Fin 3) (Fin 3) K₀ := fun i j =>
    ⟨(A : Matrix (Fin 3) (Fin 3) K) i j, (GH74.GLS.IVK.mem_fixedField_iff σ _).mpr (hfix i j)⟩
  have hM : M.map K₀.subtype = (A : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    rfl
  have hdet : M.det = 1 := by
    apply K₀.subtype_injective
    rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact A.2
  exact ⟨⟨M, hdet⟩, Subtype.ext hM⟩

theorem sl_map_subtype_injective (σ : K ≃+* K) :
    Function.Injective (SpecialLinearGroup.map (n := Fin 3)
      (GH74.GLS.IVK.fixedField σ).subtype) := by
  intro A B hAB
  ext i j
  exact congrFun (congrFun (congrArg (fun C : SpecialLinearGroup (Fin 3) K =>
    (C : Matrix (Fin 3) (Fin 3) K)) hAB) i) j

theorem card_sl_three_eq (F : Type) [Field F] [Finite F] :
    Nat.card (SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
  rw [card_SL_eq (by norm_num), show Finset.Icc 2 3 = {2, 3} by decide,
    Finset.prod_pair (by norm_num)]

theorem card_dvd_of_forall_fieldAut_eq (hK : Nat.card K % 3 = 2) (σ : K ≃+* K)
    (T : Subgroup (projectiveSL 3 K)) (hT : ∀ t ∈ T, fieldAut 3 K σ t = t) :
    Nat.card T ∣ Nat.card (SpecialLinearGroup (Fin 3) (GH74.GLS.IVK.fixedField σ)) := by
  set ρ : SpecialLinearGroup (Fin 3) (GH74.GLS.IVK.fixedField σ) →* projectiveSL 3 K :=
    (proj 3 K).comp (SpecialLinearGroup.map (GH74.GLS.IVK.fixedField σ).subtype) with hρ
  have hinj : Function.Injective ρ :=
    (proj_three_injective hK).comp (sl_map_subtype_injective σ)
  have hle : T ≤ ρ.range := by
    intro t ht
    obtain ⟨A, rfl⟩ := proj_surjective 3 K t
    obtain ⟨A₀, hA₀⟩ := exists_sl_map_subtype_eq (map_eq_of_fieldAut_proj_eq hK σ (hT _ ht))
    exact ⟨A₀, by rw [hρ, MonoidHom.comp_apply, hA₀]⟩
  calc Nat.card T ∣ Nat.card ρ.range := Subgroup.card_dvd_of_le hle
    _ = _ := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem three_mul_card_dvd_linear [Finite K] (hK : Nat.card K % 3 = 2) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) :
    3 * Nat.card (SpecialLinearGroup (Fin 3) (GH74.GLS.IVK.fixedField σ)) ∣
      Nat.card (projectiveSL 3 K) := by
  have hcard := GH74.GLS.IVK.fixedField_card_pow σ
  rw [hσ] at hcard
  have hZ : Nat.card (scalars 3 K) = 1 := by
    rw [scalars_three_eq_bot_of_mod_three hK, Subgroup.card_bot]
  rw [card_projectiveSL, hZ, Nat.div_one, card_sl_three_eq, card_sl_three_eq, ← hcard]
  refine three_mul_dvd_linear ?_ Nat.card_pos
  intro h0
  have h3 : 3 ∣ Nat.card K := by
    rw [← hcard]
    exact Dvd.dvd.pow (Nat.dvd_of_mod_eq_zero h0) (by norm_num)
  omega

end Linear

section Elements

variable {K : Type} [Field K]

theorem exists_sl_three_inverting [CharP K 2] :
    ∃ c w : SpecialLinearGroup (Fin 3) K, c ^ 3 = 1 ∧ c ≠ 1 ∧ w * c * w⁻¹ = c⁻¹ ∧
      (∀ σ : K ≃+* K, SpecialLinearGroup.map σ.toRingHom c = c) ∧
      (∀ σ : K ≃+* K, SpecialLinearGroup.map σ.toRingHom w = w) := by
  set C : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0] with hC
  set W : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 0, 1; 0, 1, 0] with hW
  have hCdet : C.det = 1 := by
    rw [hC, det_fin_three]
    simp
  have hWdet : W.det = 1 := by
    rw [hW, det_fin_three]
    simp [CharTwo.neg_eq]
  have hC3 : C * (C * C) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hC, Matrix.mul_apply, Fin.sum_univ_three]
  have hWW : W * W = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hW, Matrix.mul_apply, Fin.sum_univ_three]
  have hWCW : W * C * W = C * C := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hC, hW, Matrix.mul_apply, Fin.sum_univ_three]
  set c : SpecialLinearGroup (Fin 3) K := ⟨C, hCdet⟩ with hc
  set w : SpecialLinearGroup (Fin 3) K := ⟨W, hWdet⟩ with hw
  have hc3 : c * (c * c) = 1 := Subtype.ext hC3
  have hww : w * w = 1 := Subtype.ext hWW
  have hwcw : w * c * w = c * c := Subtype.ext hWCW
  refine ⟨c, w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_three]
    exact hc3
  · intro h
    have h00 := congrArg (fun A : SpecialLinearGroup (Fin 3) K =>
      (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp [hc, hC] at h00
  · rw [inv_eq_of_mul_eq_one_right hww, hwcw]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_assoc]; exact hc3)
  · intro σ
    refine Subtype.ext ?_
    change C.map σ = C
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hC]
  · intro σ
    refine Subtype.ext ?_
    change W.map σ = W
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hW]

theorem exists_fieldAut_fixed_inverting [CharP K 2] (hK : Nat.card K % 3 = 2) (σ : K ≃+* K) :
    ∃ x₀ y₀ : projectiveSL 3 K, fieldAut 3 K σ x₀ = x₀ ∧ fieldAut 3 K σ y₀ = y₀ ∧
      x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  obtain ⟨c, w, hc3, hc1, hwc, hcσ, hwσ⟩ := exists_sl_three_inverting (K := K)
  refine ⟨proj 3 K c, proj 3 K w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fieldAut_proj, hcσ]
  · rw [fieldAut_proj, hwσ]
  · rw [← map_pow, hc3, map_one]
  · intro h
    exact hc1 (proj_three_injective hK (h.trans (map_one _).symm))
  · rw [← map_inv, ← map_mul, ← map_mul, hwc, map_inv]

end Elements

section Data

variable {K : Type} [Field K] [Finite K]

theorem fixedData_linear [CharP K 2] (hK : Nat.card K % 3 = 2) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) :
    (∃ M : ℕ, (∀ T : Subgroup (projectiveSL 3 K), (∀ t ∈ T, fieldAut 3 K σ t = t) →
      Nat.card T ∣ M) ∧ 3 * M ∣ Nat.card (projectiveSL 3 K)) ∧
      ∃ x₀ y₀ : projectiveSL 3 K, fieldAut 3 K σ x₀ = x₀ ∧ fieldAut 3 K σ y₀ = y₀ ∧
        x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ :=
  ⟨⟨_, card_dvd_of_forall_fieldAut_eq hK σ, three_mul_card_dvd_linear hK hσ⟩,
    exists_fieldAut_fixed_inverting hK σ⟩

end Data

theorem nonempty_projSL_mulEquiv (n : ℕ) (K : Type*) [Field K] :
    Nonempty (CFSG.Assembly.RankThreeEven.projSL n K ≃* projectiveSL n K) := by
  have hrange : CFSG.Assembly.RankThreeEven.projSL n K =
      (SpecialLinearGroup.toPGL :
        SpecialLinearGroup (Fin n) K →* ProjGenLinGroup (Fin n) K).range := by
    rw [CFSG.Assembly.RankThreeEven.projSL, CFSG.Assembly.RankThreeEven.projImage,
      SpecialLinearGroup.toPGL, MonoidHom.range_comp, SpecialLinearGroup.range_toGL_eq_ker_det]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq
      (by rw [SpecialLinearGroup.toPGL_ker, scalars_eq_center] :
        scalars n K = (SpecialLinearGroup.toPGL :
          SpecialLinearGroup (Fin n) K →* ProjGenLinGroup (Fin n) K).ker)).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr hrange.symm))).symm⟩

end CFSG.RankThree.PartTwo.KFacts
