module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3
public import CFSG.RankThree.PartTwo.KFacts.K72L3Group
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.KFacts.AutPSUInner

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.GH74.GLS.IVK (fixedField)
open Matrix

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem unitaryScalars_three_eq_bot_of_mod_three (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) : unitaryScalars h 3 = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  rw [card_unitaryScalars h (by norm_num)]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)

theorem unitaryProj_three_injective (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) :
    Function.Injective (unitaryProj h 3) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_unitaryProj, unitaryScalars_three_eq_bot_of_mod_three h hq]

theorem card_unitaryPSU_three_eq_card_unitarySU (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) : Nat.card (unitaryPSU h 3) = Nat.card (unitarySU p f K 3) :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨unitaryProj_three_injective h hq,
    unitaryProj_surjective h 3⟩)).symm

theorem det_pow_succ_eq_one_of_mem_unitaryIsom3 (h : UnitaryFieldData p f K) {A : GL (Fin 3) K}
    (hA : A ∈ unitaryIsom3 h) : GeneralLinearGroup.det A ^ (p ^ f + 1) = 1 := by
  refine Units.ext ?_
  have h1 := congrArg Matrix.det (mem_unitaryIsom3.mp hA)
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_one, UnitaryFieldData.bar_apply] at h1
  rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Units.val_one, pow_succ]
  exact h1

theorem isInnerAut_of_mem_psuConj_range (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1)
    {β : MulAut (unitaryPSU h 3)} (hβ : β ∈ (psuConj h).range) : IsInnerAut β := by
  obtain ⟨A, rfl⟩ := hβ
  set d : Kˣ := GeneralLinearGroup.det (A : GL (Fin 3) K) with hd
  have hd1 : d ^ (p ^ f + 1) = 1 := det_pow_succ_eq_one_of_mem_unitaryIsom3 h A.2
  obtain ⟨m, hm⟩ : ∃ m, p ^ f + 1 = 3 * m + 2 := ⟨(p ^ f + 1) / 3, by omega⟩
  set u : Kˣ := d⁻¹ ^ (2 * m + 1) with hu
  have hu3 : u ^ 3 = d := by
    rw [hu, ← pow_mul, inv_pow, inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv, ← pow_succ,
      show (2 * m + 1) * 3 + 1 = 2 * (p ^ f + 1) by omega, pow_mul', hd1, one_pow]
  have hun : u ^ (p ^ f + 1) = 1 := by
    rw [hu, ← pow_mul, mul_comm, pow_mul, inv_pow, hd1, inv_one, one_pow]
  exact psuConj_mem_range_conj_of_det_eq_pow
    (by rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, hun, Units.val_one]) hu3.symm

theorem suField_eq_of_psuField_mk_eq (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1)
    (σ : K ≃+* K) {g : unitarySU p f K 3}
    (hg : psuField h σ (g : unitaryPSU h 3) = (g : unitaryPSU h 3)) : suField h σ g = g := by
  rw [psuField_mk] at hg
  exact unitaryProj_three_injective h hq hg

theorem card_dvd_of_forall_psuField_eq (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1)
    {σ : K ≃+* K} {f₀ : ℕ} (hf : f = 3 * f₀) (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (T : Subgroup (unitaryPSU h 3)) (hT : ∀ t ∈ T, psuField h σ t = t) :
    Nat.card T ∣ Nat.card (unitarySU p f₀ (fixedField σ) 3) := by
  have hbar := bar_coe_fixedField h hf h₀
  set ρ := (unitaryProj h 3).comp (suIncl h h₀ hbar) with hρ
  have hinj : Function.Injective ρ :=
    (unitaryProj_three_injective h hq).comp (suIncl_injective h h₀ hbar)
  have hle : T ≤ ρ.range := by
    intro t ht
    obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 t
    obtain ⟨g₀, hg₀⟩ :=
      (mem_range_suIncl_iff h h₀ hbar g).mpr (suField_eq_of_psuField_mk_eq h hq σ (hT _ ht))
    exact ⟨g₀, by rw [hρ, MonoidHom.comp_apply, hg₀]⟩
  calc Nat.card T ∣ Nat.card ρ.range := Subgroup.card_dvd_of_le hle
    _ = _ := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem three_mul_card_dvd_unitary (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1)
    {σ : K ≃+* K} {f₀ : ℕ} (hf : f = 3 * f₀) (h₀ : UnitaryFieldData p f₀ (fixedField σ)) :
    3 * Nat.card (unitarySU p f₀ (fixedField σ) 3) ∣ Nat.card (unitaryPSU h 3) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have := h₀.finite
  have := h.charP
  have := h₀.charP
  have hpow : p ^ f = (p ^ f₀) ^ 3 := by rw [hf, ← pow_mul, mul_comm]
  rw [card_unitaryPSU_three_eq_card_unitarySU h hq, unitarySU, unitarySU,
    SectionRank.OddCover.card_statedSU_three (by rw [h₀.card, ← pow_mul, mul_comm]),
    SectionRank.OddCover.card_statedSU_three (by rw [h.card, ← pow_mul, mul_comm]), hpow]
  refine three_mul_dvd_unitary ?_ (Nat.one_le_pow _ _ h.prime.pos)
  intro h0
  rw [hpow, Nat.pow_mod, h0] at hq
  norm_num at hq

end Unitary

section Elements

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_unitarySU_three_inverting [CharP K 2] (h : UnitaryFieldData p f K) :
    ∃ c w : unitarySU p f K 3, c ^ 3 = 1 ∧ c ≠ 1 ∧ w * c * w⁻¹ = c⁻¹ ∧
      (∀ σ : K ≃+* K, suField h σ c = c) ∧ (∀ σ : K ≃+* K, suField h σ w = w) := by
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
  have hC3' : C * C * C = 1 := by rw [Matrix.mul_assoc, hC3]
  have hWW : W * W = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hW, Matrix.mul_apply, Fin.sum_univ_three]
  have hWCW : W * C * W = C * C := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hC, hW, Matrix.mul_apply, Fin.sum_univ_three]
  have hCt : Cᵀ * C = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hC, Matrix.mul_apply, Fin.sum_univ_three]
  have hWt : Wᵀ * W = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hW, Matrix.mul_apply, Fin.sum_univ_three]
  have hCmap : ∀ φ : K → K, φ 0 = 0 → φ 1 = 1 → C.map φ = C := fun φ h0 h1 => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hC, h0, h1]
  have hWmap : ∀ φ : K → K, φ 0 = 0 → φ 1 = 1 → W.map φ = W := fun φ h0 h1 => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hW, h0, h1]
  set cG : GL (Fin 3) K := ⟨C, C * C, hC3, hC3'⟩ with hcG
  set wG : GL (Fin 3) K := ⟨W, W, hWW, hWW⟩ with hwG
  have hcmem : cG ∈ unitarySU p f K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨hCdet, ?_⟩
    change (C.map h.bar)ᵀ * C = 1
    rw [hCmap _ (map_zero h.bar) (map_one h.bar)]
    exact hCt
  have hwmem : wG ∈ unitarySU p f K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨hWdet, ?_⟩
    change (W.map h.bar)ᵀ * W = 1
    rw [hWmap _ (map_zero h.bar) (map_one h.bar)]
    exact hWt
  set c : unitarySU p f K 3 := ⟨cG, hcmem⟩ with hc
  set w : unitarySU p f K 3 := ⟨wG, hwmem⟩ with hw
  have hc3 : c * (c * c) = 1 := Subtype.ext (Units.ext hC3)
  have hww : w * w = 1 := Subtype.ext (Units.ext hWW)
  have hwcw : w * c * w = c * c := Subtype.ext (Units.ext hWCW)
  refine ⟨c, w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_three]
    exact hc3
  · intro h1
    have h00 := congrArg (fun A : unitarySU p f K 3 =>
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp [hc, hcG, hC] at h00
  · rw [inv_eq_of_mul_eq_one_right hww, hwcw]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_assoc]; exact hc3)
  · intro σ
    apply Subtype.ext
    apply Units.ext
    rw [coe_suField, coe_glAut]
    exact hCmap σ (map_zero σ) (map_one σ)
  · intro σ
    apply Subtype.ext
    apply Units.ext
    rw [coe_suField, coe_glAut]
    exact hWmap σ (map_zero σ) (map_one σ)

theorem exists_psuField_fixed_inverting [CharP K 2] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) (σ : K ≃+* K) :
    ∃ x₀ y₀ : unitaryPSU h 3, psuField h σ x₀ = x₀ ∧ psuField h σ y₀ = y₀ ∧
      x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  obtain ⟨c, w, hc3, hc1, hwc, hcσ, hwσ⟩ := exists_unitarySU_three_inverting h
  refine ⟨unitaryProj h 3 c, unitaryProj h 3 w, ?_, ?_, ?_, ?_, ?_⟩
  · exact (psuField_mk σ c).trans (congrArg (unitaryProj h 3) (hcσ σ))
  · exact (psuField_mk σ w).trans (congrArg (unitaryProj h 3) (hwσ σ))
  · rw [← map_pow, hc3, map_one]
  · intro h1
    exact hc1 (unitaryProj_three_injective h hq (h1.trans (map_one _).symm))
  · rw [← map_inv, ← map_mul, ← map_mul, hwc, map_inv]

end Elements

theorem fixedData_unitary {p f : ℕ} {K : Type} [Field K] [CharP K 2] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    (∃ M : ℕ, (∀ T : Subgroup (unitaryPSU h 3), (∀ t ∈ T, psuField h σ t = t) →
      Nat.card T ∣ M) ∧ 3 * M ∣ Nat.card (unitaryPSU h 3)) ∧
      ∃ x₀ y₀ : unitaryPSU h 3, psuField h σ x₀ = x₀ ∧ psuField h σ y₀ = y₀ ∧
        x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData p f₀ (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  exact ⟨⟨_, card_dvd_of_forall_psuField_eq h hq hf h₀, three_mul_card_dvd_unitary h hq hf h₀⟩,
    exists_psuField_fixed_inverting h hq σ⟩

theorem nonempty_unitaryPSU_mulEquiv_projSU {p f : ℕ} [Fact p.Prime]
    (h : UnitaryFieldData p f (GaloisField p (2 * f))) :
    Nonempty (unitaryPSU h 3 ≃* CFSG.Assembly.RankThreeEven.projSU 3 p f) :=
  ⟨(unitaryPSUEquiv h (by norm_num)).trans ((Census.statedProjEquivProjImage _).trans
    (MulEquiv.subgroupCongr (Census.projImage_statedSU 3 p f)))⟩

end CFSG.RankThree.PartTwo.KFacts
