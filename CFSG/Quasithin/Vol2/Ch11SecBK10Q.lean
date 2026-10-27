module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutBasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.U3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem inv_apply_self {g : GL (HypIndex r ε) K}
    (hg : (g : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular fullPos)
    (a : HypIndex r ε) :
    (g : Matrix (HypIndex r ε) (HypIndex r ε) K) a a *
      ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a = 1 := by
  have := mul_apply_self_of_blockTriangular fullPos_injective hg (blockTriangular_inv_fullPos hg) a
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply_eq] at this
  exact this.symm

theorem commutator_mem_fullUnitriangular {g₁ g₂ : GL (HypIndex r ε) K}
    (h₁ : (g₁ : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular fullPos)
    (h₂ : (g₂ : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular fullPos) :
    g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ fullUnitriangular r ε K := by
  have i₁ := blockTriangular_inv_fullPos h₁
  have i₂ := blockTriangular_inv_fullPos h₂
  refine ⟨?_, fun a => ?_⟩
  · simp only [Units.val_mul]
    exact ((h₁.mul h₂).mul i₁).mul i₂
  · simp only [Units.val_mul]
    rw [mul_apply_self_of_blockTriangular fullPos_injective ((h₁.mul h₂).mul i₁) i₂,
      mul_apply_self_of_blockTriangular fullPos_injective (h₁.mul h₂) i₁,
      mul_apply_self_of_blockTriangular fullPos_injective h₁ h₂]
    have e₁ := inv_apply_self h₁ a
    have e₂ := inv_apply_self h₂ a
    linear_combination (((g₂ : Matrix (HypIndex r ε) (HypIndex r ε) K) a a) *
      ((g₂⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a) * e₁ + e₂

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def simRight : semilinearSimilitudes h 1 1 →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (semilinearSimilitudes h 1 1).subtype

theorem ker_le : (semilinearAutHom h (le_refl 1) (le_refl 1)).ker ≤ (simRight h).ker :=
  fun x hx => ((semilinearAutHom_eq_one_iff h (le_refl 1) (le_refl 1) (by norm_num) x).mp hx).1

@[expose] noncomputable def galPart (hq : ¬(2 * 1 + 1 = 3 ∧ p ^ f = 2)) :
    MulAut (hypPSU h 1 1) →* (K ≃+* K) :=
  (QuotientGroup.lift _ (simRight h) (ker_le h)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (semilinearAutHom_surjective_of_admissible h (le_refl 1) (le_refl 1) (by norm_num)
        hq)).symm.toMonoidHom

theorem galPart_apply (hq : ¬(2 * 1 + 1 = 3 ∧ p ^ f = 2)) (x : semilinearSimilitudes h 1 1) :
    galPart h hq (semilinearAutHom h (le_refl 1) (le_refl 1) x) =
      (x : SemiGL (HypIndex 1 1) K).right := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective _
      (semilinearAutHom_surjective_of_admissible h (le_refl 1) (le_refl 1) (by norm_num)
        hq)).symm (semilinearAutHom h (le_refl 1) (le_refl 1) x) = QuotientGroup.mk x := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [galPart, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  rfl

theorem inr_mem (σ : K ≃+* K) : SemidirectProduct.inr σ ∈ semilinearSimilitudes h 1 1 :=
  ⟨1, one_ne_zero, map_one _, by
    rw [SemidirectProduct.left_inr, Units.val_one, Matrix.map_one _ (map_zero h.bar)
      (map_one h.bar), transpose_one, Matrix.one_mul, Matrix.mul_one, one_smul]⟩

theorem inl_mem {x : SemiGL (HypIndex 1 1) K} (hx : x ∈ semilinearSimilitudes h 1 1) :
    SemidirectProduct.inl x.left ∈ semilinearSimilitudes h 1 1 := by
  obtain ⟨μ, hμ0, hμ, hA⟩ := hx
  exact ⟨μ, hμ0, hμ, by rwa [SemidirectProduct.left_inl]⟩

@[expose] noncomputable def fieldAutHom : (K ≃+* K) →* MulAut (hypPSU h 1 1) :=
  (semilinearAutHom h (le_refl 1) (le_refl 1)).comp
    ((SemidirectProduct.inr).codRestrict _ (inr_mem h))

theorem fieldAutHom_apply (σ : K ≃+* K) (g : hypSU h 1 1) :
    ∃ hg : glAut σ (g : GL (HypIndex 1 1) K) ∈ hypSU h 1 1,
      fieldAutHom h σ (hypProj h 1 1 g) = hypProj h 1 1 ⟨_, hg⟩ := by
  have e := semilinearAutHom_apply h (le_refl 1) (le_refl 1) ⟨_, inr_mem h σ⟩ g
  have e' : (SemidirectProduct.inr σ : SemiGL (HypIndex 1 1) K).left *
      glAut (SemidirectProduct.inr σ : SemiGL (HypIndex 1 1) K).right
        (g : GL (HypIndex 1 1) K) * (SemidirectProduct.inr σ : SemiGL (HypIndex 1 1) K).left⁻¹ =
      glAut σ (g : GL (HypIndex 1 1) K) := by
    rw [SemidirectProduct.left_inr, SemidirectProduct.right_inr, inv_one, one_mul, mul_one]
  have hg : glAut σ (g : GL (HypIndex 1 1) K) ∈ hypSU h 1 1 := e' ▸ conj_mem_hypSU (inr_mem h σ) g
  refine ⟨hg, ?_⟩
  refine e.trans (congrArg (hypProj h 1 1) (Subtype.ext ?_))
  exact e'

theorem fieldAutHom_mem (σ : K ≃+* K) {u : hypPSU h 1 1}
    (hu : u ∈ hypProjUnitriangular h 1 1) : fieldAutHom h σ u ∈ hypProjUnitriangular h 1 1 := by
  obtain ⟨g, hg, rfl⟩ := hu
  obtain ⟨hg', e⟩ := fieldAutHom_apply h σ g
  rw [e]
  refine ⟨_, ?_, rfl⟩
  obtain ⟨hgT, hgD⟩ := mem_hypUnitriangular.mp hg
  refine mem_hypUnitriangular.mpr ⟨fun i j hij => ?_, fun a => ?_⟩
  · change ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map σ i j = 0
    rw [Matrix.map_apply, hgT hij, map_zero]
  · change ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map σ a a = 1
    rw [Matrix.map_apply, hgD a, map_one]

theorem semilinearAutHom_eq_mul (x : semilinearSimilitudes h 1 1) :
    semilinearAutHom h (le_refl 1) (le_refl 1) x =
      semilinearAutHom h (le_refl 1) (le_refl 1) ⟨_, inl_mem h x.2⟩ *
        fieldAutHom h (x : SemiGL (HypIndex 1 1) K).right := by
  rw [fieldAutHom, MonoidHom.comp_apply, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (SemidirectProduct.inl_left_mul_inr_right _).symm

theorem semilinearAutHom_eq_conj {x : semilinearSimilitudes h 1 1}
    (hx : (x : SemiGL (HypIndex 1 1) K).right = 1)
    (hA : (x : SemiGL (HypIndex 1 1) K).left ∈ hypSU h 1 1) :
    semilinearAutHom h (le_refl 1) (le_refl 1) x = MulAut.conj (hypProj h 1 1 ⟨_, hA⟩) := by
  ext y
  obtain ⟨g, rfl⟩ := hypProj_surjective h 1 1 y
  rw [semilinearAutHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change _ * glAut (x : SemiGL (HypIndex 1 1) K).right (g : GL (HypIndex 1 1) K) * _ = _
  rw [hx, map_one, MulAut.one_apply]
  rfl

theorem norm_eq_one_iff {c : Kˣ} : h.norm (c : K) = 1 ↔ c ^ (p ^ f + 1) = 1 := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ', Units.ext_iff,
    Units.val_pow_eq_pow_val, Units.val_one]

theorem exists_cube_root (h3 : ¬ 3 ∣ p ^ f + 1) {a : Kˣ} (ha : h.norm (a : K) = 1) :
    ∃ d : Kˣ, h.norm (d : K) = 1 ∧ d ^ 3 * a = 1 := by
  have ha' := (norm_eq_one_iff h).mp ha
  have hcop : Nat.Coprime 3 (orderOf a⁻¹) := by
    rw [orderOf_inv]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one ha')
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨a⁻¹ ^ m, (norm_eq_one_iff h).mpr ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, inv_pow, ha', inv_one, one_pow]
  · rw [← pow_mul, mul_comm m 3, pow_mul, hm, inv_mul_cancel]

theorem semilinearAutHom_mem_inner (h3 : ¬ 3 ∣ p ^ f + 1) {x : semilinearSimilitudes h 1 1}
    (hx : (x : SemiGL (HypIndex 1 1) K).right = 1) :
    semilinearAutHom h (le_refl 1) (le_refl 1) x ∈ inner (hypPSU h 1 1) := by
  obtain ⟨x₁, hx₁, hσ₁, hU⟩ := exists_unitary_rep h (le_refl 1) (le_refl 1) (by norm_num) x
  set A : GL (HypIndex 1 1) K := (x₁ : SemiGL (HypIndex 1 1) K).left with hA
  set a : Kˣ := Units.mk0 (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det
    (Matrix.isUnits_det_units A).ne_zero with ha
  have hNa : h.norm (a : K) = 1 := QuasithinUnique.Ch1.norm_det_eq_one_of_mem_hypUnitary h hU
  obtain ⟨d, hNd, hd3⟩ := exists_cube_root h h3 hNa
  set s : semilinearSimilitudes h 1 1 := ⟨_, scalarSim_mem h d⟩ with hs
  have hs1 : semilinearAutHom h (le_refl 1) (le_refl 1) s = 1 :=
    (semilinearAutHom_eq_one_iff h (le_refl 1) (le_refl 1) (by norm_num) s).mpr
      ⟨rfl, d, rfl⟩
  have hleft : ((s * x₁ : semilinearSimilitudes h 1 1) : SemiGL (HypIndex 1 1) K).left =
      GeneralLinearGroup.scalar (HypIndex 1 1) d * A := by
    change (SemidirectProduct.inl (GeneralLinearGroup.scalar (HypIndex 1 1) d) *
      (x₁ : SemiGL (HypIndex 1 1) K)).left = _
    rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      map_one, MulAut.one_apply]
  have hright : ((s * x₁ : semilinearSimilitudes h 1 1) : SemiGL (HypIndex 1 1) K).right = 1 := by
    change (SemidirectProduct.inl (GeneralLinearGroup.scalar (HypIndex 1 1) d) *
      (x₁ : SemiGL (HypIndex 1 1) K)).right = _
    rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul, hσ₁, hx]
  have hmem : ((s * x₁ : semilinearSimilitudes h 1 1) : SemiGL (HypIndex 1 1) K).left ∈
      hypSU h 1 1 := by
    rw [hleft]
    refine mem_hypSU.mpr ⟨?_, ?_⟩
    · rw [Units.val_mul, conjTranspose_mul_mul, GeneralLinearGroup.coe_scalar, scalar_gram,
        Matrix.mul_smul, Matrix.smul_mul, mem_hypUnitary.mp hU, hNd, one_smul]
    · rw [Units.val_mul, Matrix.det_mul, QuasithinUnique.Ch1.det_scalar_hypIndex]
      have := congrArg Units.val hd3
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] at this
      exact this
  rw [← hx₁, ← one_mul (semilinearAutHom h (le_refl 1) (le_refl 1) x₁), ← hs1, ← map_mul,
    semilinearAutHom_eq_conj h hright hmem]
  exact ⟨_, rfl⟩

theorem hypScalars_eq_bot (h3 : ¬ 3 ∣ p ^ f + 1) : hypScalars h 1 1 = ⊥ := by
  have : Finite K := h.finite
  apply Subgroup.eq_bot_of_card_eq
  rw [card_hypScalars h (by norm_num)]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3

theorem hypProj_injective (h3 : ¬ 3 ∣ p ^ f + 1) : Function.Injective (hypProj h 1 1) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_hypProj, hypScalars_eq_bot h h3]

end BK10.U3

end CFSG.Quasithin.Vol2.Ch11.SecD
