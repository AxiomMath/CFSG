module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4Fld
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K)

private theorem uc22s218_u4_ls_eq_one_of_pow_four [CharP K 2] {c : K} (hc : c ^ 4 = 1) : c = 1 := by
  have h2 : c ^ 2 = 1 := CharTwo.sq_inj.mp (by rw [← pow_mul, one_pow]; exact hc)
  exact CharTwo.sq_inj.mp (by rw [one_pow]; exact h2)

theorem uc22s218_u4_ls_exists_conj_eq {A : GL (Fin 4) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    ∃ s : ↥(unitarySU 2 n K 4), ∀ g : GL (Fin 4) K,
      (s : GL (Fin 4) K) * g * (s : GL (Fin 4) K)⁻¹ = A * g * A⁻¹ := by
  have := h.finite
  have := h.charP
  have hδ0 : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  obtain ⟨c, hc⟩ : ∃ c : K, c ^ 4 = (A : Matrix (Fin 4) (Fin 4) K).det := by
    obtain ⟨a, ha⟩ := isSquare_of_charTwo' (A : Matrix (Fin 4) (Fin 4) K).det
    obtain ⟨b, hb⟩ := isSquare_of_charTwo' a
    exact ⟨b, by rw [ha, hb]; ring⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hδ0 (by rw [← hc]; norm_num)
  have hcN : h.norm c = 1 := by
    apply uc22s218_u4_ls_eq_one_of_pow_four
    rw [UnitaryFieldData.norm, mul_pow, ← map_pow, hc]
    exact norm_det_eq_one h 1 hA
  set z : GL (Fin 4) K := Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 c hc0)⁻¹ with hzdef
  have hz : z ∈ primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [mem_primeFormUnitary, hzdef, Matrix.GeneralLinearGroup.coe_scalar,
      scalar_barTranspose_mul_mul, Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv_eq, hcN,
      inv_one, one_smul]
  have hdet : ((z * A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hzdef, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hc]
    exact inv_mul_cancel₀ hδ0
  refine ⟨⟨z * A, (unitarySU_eq_gramSU h 4).symm ▸
    (mem_gramSU_iff_unitary (h := h)).2 ⟨mul_mem hz hA, hdet⟩⟩, fun g => ?_⟩
  have hzc : ∀ y : GL (Fin 4) K, z * y = y * z := fun y =>
    (commute_scalar (Units.mk0 c hc0)⁻¹ y).eq.symm
  change z * A * g * (z * A)⁻¹ = A * g * A⁻¹
  calc z * A * g * (z * A)⁻¹ = z * (A * g * A⁻¹) * z⁻¹ := by group
    _ = (A * g * A⁻¹) * z * z⁻¹ := by rw [hzc]
    _ = A * g * A⁻¹ := by group

private theorem uc22s218_u4_ls_mem_gramSU (s : ↥(unitarySU 2 n K 4)) :
    (s : GL (Fin 4) K) ∈ gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  (unitarySU_eq_gramSU h 4) ▸ s.2

private noncomputable def uc22s218_u4_ls_proj :
    ↥(unitarySU 2 n K 4) →* primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) where
  toFun s := ((⟨s, uc22s218_u4_ls_mem_gramSU h s⟩ : gramSU h ((1 : GL (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K)) : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem uc22s218_u4_ls_proj_bijective : Function.Bijective (uc22s218_u4_ls_proj h) := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun s hs => ?_, fun y => ?_⟩
  · obtain ⟨c, -, hc4, hc⟩ := (QuotientGroup.eq_one_iff _).mp hs
    have := h.charP
    have hc1 : c = 1 := Units.ext (uc22s218_u4_ls_eq_one_of_pow_four (by
      rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]))
    subst hc1
    exact Subtype.ext (by rw [map_one] at hc; exact hc)
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨g, (unitarySU_eq_gramSU h 4).symm ▸ g.2⟩, rfl⟩

private noncomputable def uc22s218_u4_ls_projEquiv :
    ↥(unitarySU 2 n K 4) ≃* primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  MulEquiv.ofBijective (uc22s218_u4_ls_proj h) (uc22s218_u4_ls_proj_bijective h)

private theorem uc22s218_u4_ls_projEquiv_apply (s : ↥(unitarySU 2 n K 4)) :
    uc22s218_u4_ls_projEquiv h s =
      ((⟨s, uc22s218_u4_ls_mem_gramSU h s⟩ : gramSU h ((1 : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)) :
        primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :=
  rfl

private theorem uc22s218_u4_ls_congr_conj (s : ↥(unitarySU 2 n K 4)) :
    MulAut.congr (uc22s218_u4_ls_projEquiv h) (MulAut.conj s) =
      primeFormConjHom h _ ⟨(s : GL (Fin 4) K), (uc22s218_u4_ls_mem_gramSU h s).1⟩ := by
  refine Eq.trans ?_ (primeFormConjHom_eq_conj h _
    ⟨(s : GL (Fin 4) K), uc22s218_u4_ls_mem_gramSU h s⟩).symm
  ext y
  simp [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply]
  rfl

private theorem uc22s218_u4_ls_congr_field (hC : IsPrimeFormGram (1 : GL (Fin 4) K))
    (θ : K ≃+* K) :
    MulAut.congr (uc22s218_u4_ls_projEquiv h) (uc22s218_u4_field h θ) =
      primeFormFieldHom h hC θ := by
  ext y
  obtain ⟨t, rfl⟩ := (uc22s218_u4_ls_projEquiv h).surjective y
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    uc22s218_u4_ls_projEquiv_apply h t]
  show _ = primeFormFieldAut h hC θ _
  rw [primeFormFieldAut_mk]
  rfl

private theorem uc22s218_u4_ls_conjHom_eq
    (A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    ∃ s : ↥(unitarySU 2 n K 4), primeFormConjHom h _ A =
      MulAut.congr (uc22s218_u4_ls_projEquiv h) (MulAut.conj s) := by
  obtain ⟨s, hs⟩ := uc22s218_u4_ls_exists_conj_eq h A.2
  refine ⟨s, ?_⟩
  rw [uc22s218_u4_ls_congr_conj h s]
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [primeFormConjHom_mk, primeFormConjHom_mk]
  congr 1
  exact Subtype.ext (hs g).symm

theorem uc22s218_u4_aut_structure :
    ∃ τ : MulAut ↥(unitarySU 2 n K 4) →* (K ≃+* K),
      (∀ θ, τ (uc22s218_u4_field h θ) = θ) ∧
      (∀ α, τ α = 1 → ∃ s : ↥(unitarySU 2 n K 4), α = MulAut.conj s) ∧
      (∀ s : ↥(unitarySU 2 n K 4), τ (MulAut.conj s) = 1) ∧
      ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ α : MulAut ↥(unitarySU 2 n K 4), α ^ p = 1 → τ α ≠ 1 →
        orderOf (τ α) = p ∧ ∃ s : ↥(unitarySU 2 n K 4),
          α = MulAut.conj s * uc22s218_u4_field h (τ α) * (MulAut.conj s)⁻¹ := by
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := isPrimeFormGram_one
  have hn : 3 ≤ 4 := by norm_num
  have hq : ¬(4 = 3 ∧ 2 ^ n = 2) := fun hh => absurd hh.1 (by norm_num)
  set κ := uc22s218_u4_ls_projEquiv h
  set Φ := primeFormFieldFactor h hC hn hq with hΦ
  refine ⟨Φ.comp (MulAut.congr κ).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro θ
    change Φ (MulAut.congr κ (uc22s218_u4_field h θ)) = θ
    have := primeFormFieldFactor_apply h hC hn hq 1 θ
    rwa [map_one, one_mul, ← uc22s218_u4_ls_congr_field h hC] at this
  · intro α hα
    have h1 : MulAut.congr κ α ∈ Φ.ker := hα
    rw [hΦ, ker_primeFormFieldFactor h hC hn hq] at h1
    obtain ⟨A, hA⟩ := h1
    obtain ⟨s, hs⟩ := uc22s218_u4_ls_conjHom_eq h A
    exact ⟨s, (MulAut.congr κ).injective (hA.symm.trans hs)⟩
  · intro s
    change Φ (MulAut.congr κ (MulAut.conj s)) = 1
    rw [uc22s218_u4_ls_congr_conj h s]
    have := primeFormFieldFactor_apply h hC hn hq
      ⟨(s : GL (Fin 4) K), (uc22s218_u4_ls_mem_gramSU h s).1⟩ 1
    rwa [map_one, mul_one] at this
  · intro p hp hp2 α hαp hτ
    set β := MulAut.congr κ α with hβ
    have hβp : β ^ p = 1 := by rw [hβ, ← map_pow, hαp, map_one]
    obtain ⟨⟨A, θ⟩, hAθ⟩ := primeFormPsi_surjective h hC hn hq β
    rw [primeFormPsi_apply] at hAθ
    have hτα : (Φ.comp (MulAut.congr κ).toMonoidHom) α = θ := by
      change Φ β = θ
      rw [← hAθ]
      exact primeFormFieldFactor_apply h hC hn hq A θ
    rw [hτα] at hτ ⊢
    obtain ⟨hθo, H, hH⟩ := CFSG.StandardType.RecipeFieldSpU.primeForm_conj_of_pow_eq_one h hn hq
      hp hp2 A θ hτ (by rw [hAθ]; exact hβp)
    obtain ⟨s, hs⟩ := uc22s218_u4_ls_conjHom_eq h H
    refine ⟨hθo, s, (MulAut.congr κ).injective ?_⟩
    rw [map_mul, map_mul, map_inv, ← hs, uc22s218_u4_ls_congr_field h hC, ← hH, hAθ]

end CFSG.LocalAnalysis.UniquenessCase.UC22
