module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddGL2
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.RankThree.PartTwo.Sec4.L34Odd

open CFSG.GorensteinWalter

section Block

variable {K : Type*} [Field K]

@[expose] def blockMat (A : Matrix (Fin 2) (Fin 2) K) (d : K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, d]

theorem det_blockMat (A : Matrix (Fin 2) (Fin 2) K) (d : K) :
    (blockMat A d).det = A.det * d := by
  simp [blockMat, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem blockMat_mul (A B : Matrix (Fin 2) (Fin 2) K) (d e : K) :
    blockMat A d * blockMat B e = blockMat (A * B) (d * e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockMat_one : blockMat (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, Matrix.one_apply]

@[expose] noncomputable def embSLFun (A : GL (Fin 2) K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨blockMat (A : Matrix (Fin 2) (Fin 2) K) ((A : Matrix (Fin 2) (Fin 2) K).det)⁻¹, by
    rw [det_blockMat]
    exact mul_inv_cancel₀ (Matrix.GeneralLinearGroup.det_ne_zero A)⟩

theorem embSLFun_coe (A : GL (Fin 2) K) :
    ((embSLFun A : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockMat (A : Matrix (Fin 2) (Fin 2) K) ((A : Matrix (Fin 2) (Fin 2) K).det)⁻¹ := rfl

theorem embSLFun_one : embSLFun (1 : GL (Fin 2) K) = 1 := by
  apply Subtype.ext
  rw [embSLFun_coe, Matrix.SpecialLinearGroup.coe_one]
  simp [blockMat_one]

theorem embSLFun_mul (A B : GL (Fin 2) K) : embSLFun (A * B) = embSLFun A * embSLFun B := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, embSLFun_coe, embSLFun_coe, embSLFun_coe, blockMat_mul,
    Units.val_mul, Matrix.det_mul, mul_inv]

@[expose] noncomputable def embSL : GL (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 3) K where
  toFun := embSLFun
  map_one' := embSLFun_one
  map_mul' := embSLFun_mul

theorem embSL_coe (A : GL (Fin 2) K) :
    ((embSL A : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockMat (A : Matrix (Fin 2) (Fin 2) K) ((A : Matrix (Fin 2) (Fin 2) K).det)⁻¹ := rfl

theorem embSL_injective : Function.Injective (embSL (K := K)) := by
  intro A B h
  have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [embSL_coe] at h'
  have e00 := congrFun (congrFun h' 0) 0
  have e01 := congrFun (congrFun h' 0) 1
  have e10 := congrFun (congrFun h' 1) 0
  have e11 := congrFun (congrFun h' 1) 1
  simp [blockMat] at e00 e01 e10 e11
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

end Block

section Index

variable {K : Type*} [Field K] [Finite K]

theorem card_embSL_range_index :
    (embSL (K := K)).range.index =
      (Nat.card K) ^ 2 * ((Nat.card K) ^ 2 + Nat.card K + 1) := by
  haveI : Fintype K := Fintype.ofFinite K
  set q := Nat.card K with hq
  have hqc : Fintype.card K = q := (Nat.card_eq_fintype_card).symm
  have hq2 : 2 ≤ q := by
    rw [hq]
    exact Nat.succ_le_of_lt Finite.one_lt_card
  have hGL3 : Nat.card (GL (Fin 3) K) = (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) := by
    rw [Matrix.card_GL_field, hqc]
    simp [Fin.prod_univ_three]
  have hGL2 : Nat.card (GL (Fin 2) K) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    rw [Matrix.card_GL_field, hqc]
    simp [Fin.prod_univ_two]
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) * (q - 1) = Nat.card (GL (Fin 3) K) := by
    have := Matrix.card_SL_mul_card_units (n := Fin 3) (R := K)
    rwa [Nat.card_units] at this
  have hrange : Nat.card (embSL (K := K)).range = Nat.card (GL (Fin 2) K) :=
    (Nat.card_congr (MonoidHom.ofInjective (embSL_injective (K := K))).toEquiv).symm
  have hidx := Subgroup.card_mul_index (embSL (K := K)).range
  rw [hrange, hGL2] at hidx
  have hq1 : 1 ≤ q := by omega
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h3 : q ^ 2 ≤ q ^ 3 := by nlinarith [Nat.zero_le (q ^ 2)]
  have h4 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h5 : q ≤ q ^ 3 := h2.trans h3
  have hpos : 0 < (q ^ 2 - 1) * (q ^ 2 - q) := by
    apply Nat.mul_pos
    · have : 4 ≤ q ^ 2 := by nlinarith
      omega
    · have : q + 2 ≤ q ^ 2 := by nlinarith
      omega
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hidx]
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  rw [hSL, hGL3]
  zify [h1, h2, h3, h4, h5, hq1]
  ring

theorem not_two_dvd_card_embSL_range_index (hK : Odd (Nat.card K)) :
    ¬ 2 ∣ (embSL (K := K)).range.index := by
  rw [card_embSL_range_index]
  have h1 : Odd ((Nat.card K) ^ 2 + Nat.card K + 1) :=
    ((hK.pow (n := 2)).add_odd hK).add_one
  have h2 : Odd ((Nat.card K) ^ 2 * ((Nat.card K) ^ 2 + Nat.card K + 1)) :=
    (hK.pow (n := 2)).mul h1
  exact Nat.not_even_iff_odd.2 h2 ∘ even_iff_two_dvd.2

end Index

theorem exists_conj_map_le_sylow_aux {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {E : Subgroup G} (hE : IsPGroup p E) :
    ∃ c : G, E.map (MulAut.conj c).toMonoidHom ≤ (P : Subgroup G) := by
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxQ : x ∈ ((g • P : Sylow p G) : Subgroup G) := by rw [hg]; exact hEQ hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hsx
  have : (MulAut.conj g⁻¹).toMonoidHom x = s := by
    rw [← hsx]; simp; group
  rw [this]; exact hs

theorem exists_conj_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (M : Subgroup G) (hM : ¬ p ∣ M.index) {R : Subgroup G} (hR : IsPGroup p R) :
    ∃ c : G, R.map (MulAut.conj c).toMonoidHom ≤ M := by
  obtain ⟨S0⟩ : Nonempty (Sylow p M) := inferInstance
  set S1 : Subgroup G := (S0 : Subgroup M).map M.subtype with hS1def
  have hS1 : IsPGroup p S1 := S0.isPGroup'.map M.subtype
  have hidx : ¬ p ∣ S1.index := by
    rw [hS1def, Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
    · exact S0.not_dvd_index h
    · exact hM h
  obtain ⟨c, hc⟩ := exists_conj_map_le_sylow_aux (hS1.toSylow hidx) hR
  refine ⟨c, hc.trans ?_⟩
  rw [IsPGroup.toSylow_coe]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem exists_injective_gl2 {K : Type*} [Field K] [Finite K] (hK : Odd (Nat.card K))
    {S : Type*} [Group S] (hS : IsPGroup 2 S) (τ : S →* Matrix.SpecialLinearGroup (Fin 3) K)
    (hτ : Function.Injective τ) : ∃ σ : S →* GL (Fin 2) K, Function.Injective σ := by
  have hR : IsPGroup 2 τ.range := hS.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  obtain ⟨c, hc⟩ := exists_conj_le_of_not_dvd_index (p := 2) (embSL (K := K)).range
    (not_two_dvd_card_embSL_range_index hK) hR
  have hmem : ∀ s : S, (MulAut.conj c).toMonoidHom (τ s) ∈ (embSL (K := K)).range := fun s =>
    hc ⟨τ s, ⟨s, rfl⟩, rfl⟩
  let e := MonoidHom.ofInjective (embSL_injective (K := K))
  let τ' : S →* (embSL (K := K)).range :=
    ((MulAut.conj c).toMonoidHom.comp τ).codRestrict _ hmem
  refine ⟨e.symm.toMonoidHom.comp τ', ?_⟩
  intro s t hst
  have h1 : τ' s = τ' t := e.symm.injective hst
  have h2 : (MulAut.conj c).toMonoidHom (τ s) = (MulAut.conj c).toMonoidHom (τ t) :=
    congrArg Subtype.val h1
  exact hτ ((MulAut.conj c).injective h2)

theorem gl2Type_of_injective_sl3 {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) {S : Type*} [Group S] (hS : IsPGroup 2 S)
    (τ : S →* Matrix.SpecialLinearGroup (Fin 3) K) (hτ : Function.Injective τ) : GL2Type S := by
  obtain ⟨σ, hσ⟩ := exists_injective_gl2 (odd_card_of_isOddPrimePower hK) hS τ hτ
  exact gl2Type_of_injective hK σ hσ hS

end CFSG.RankThree.PartTwo.Sec4.L34Odd

end
