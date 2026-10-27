module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4SmallProofCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGD4FieldFixTorus : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ φ : MulAut R, φ ^ 3 = 1 → φ ∉ (MulAut.conj : R →* MulAut R).range →
      (∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f) →
      ∃ E W : Subgroup R, IsElemAbelian 3 E ∧ Nat.card E = 81 ∧ (∀ e ∈ E, φ e = e) ∧
        IsPGroup 2 W ∧ W ≠ ⊥ ∧ (∀ w ∈ W, φ w ∈ W) ∧ ∀ e ∈ E, ∀ w ∈ W, e * w * e⁻¹ ∈ W

namespace NbrGraphD4Torus

open TableBSymp

variable {K : Type} [Field K] {m : ℕ}

theorem diagGL_pairedUnits_map (σ : K ≃+* K) {u : Fin m → Kˣ} (hu : ∀ i, σ (u i : K) = u i) :
    ((TauCeti.diagGL (pairedUnits u) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ =
      ((TauCeti.diagGL (pairedUnits u) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
  rw [TauCeti.diagGL_coe, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext x
  rcases x with i | i
  · exact hu i
  · change σ (((u i)⁻¹ : Kˣ) : K) = (((u i)⁻¹ : Kˣ) : K)
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu i]

theorem map_zmodPowHom {p : ℕ} [NeZero p] (σ : K ≃+* K) {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (hσ : σ (ζ : K) = ζ) (a : Multiplicative (ZMod p)) :
    σ ((zmodPowHom hζ a : Kˣ) : K) = (zmodPowHom hζ a : Kˣ) := by
  rw [zmodPowHom_apply hζ a, Units.val_pow_eq_pow_val, map_pow, hσ]

theorem spTorusGL_map {p : ℕ} [NeZero p] (σ : K ≃+* K) {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (hσ : σ (ζ : K) = ζ) (f : Fin m → Multiplicative (ZMod p)) :
    ((spTorusGL hζ f : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ =
      ((spTorusGL hζ f : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
  rw [spTorusGL_apply]
  exact diagGL_pairedUnits_map σ fun i => map_zmodPowHom σ hζ hσ (f i)

theorem siegelMat_map (σ : K ≃+* K) (i₀ i₁ : Fin m) (c : K) :
    (siegelMat i₀ i₁ c).map σ = siegelMat (K := K) i₀ i₁ (σ c) := by
  ext (i | i) (j | j) <;>
    simp [siegelMat, siegelS, Matrix.one_apply, Matrix.single_apply, apply_ite σ]

theorem eq_zero_of_siegelGL_mem_scalars {i₀ i₁ : Fin m} (h01 : i₁ ≠ i₀) {c : K}
    (h : siegelGL i₀ i₁ c ∈ LargeEvenScalars (Fin m ⊕ Fin m) K) : c = 0 := by
  obtain ⟨u, hu⟩ := h
  have e := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl i₀) (Sum.inr i₁)) hu
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_siegelGL, siegelMat,
    siegelS, h01, Ne.symm h01] at e
  exact e.symm

theorem map_eq_of_cube [CharP K 2] (σ : K ≃+* K) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0)
    (h3 : σ (σ (σ ζ)) = ζ) : σ ζ = ζ := by
  have hσζ : σ ζ ^ 2 + σ ζ + 1 = 0 := by
    have := congrArg σ hζ
    rwa [map_add, map_add, map_pow, map_one, map_zero] at this
  have hprod : (σ ζ - ζ) * (σ ζ + ζ + 1) = 0 := by linear_combination hσζ - hζ
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have h1 : σ ζ = -ζ - 1 := by linear_combination h
    have h2 : σ (σ ζ) = ζ := by
      rw [h1, map_sub, map_neg, map_one, h1]
      ring
    rw [h2, h1] at h3
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (1 : K) = 0 := by linear_combination -h3 - ζ * h22
    exact one_ne_zero this

section Main

variable [Finite K] [CharP K 2]

local notation "H₈" => LargeEvenOmega (LargeEvenQPlus K 4)

local notation "π₈" => LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4))

theorem ggD4FieldFixTorus_omegaPlus (h3 : 3 ∣ Nat.card K - 1) :
    GGD4FieldFixTorus (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro hs hna φ hφ3 hφI hφIF
  obtain ⟨u, hu, f, hf, hφ⟩ := hφIF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f', ⟨σ, hσ⟩, u', -, hf'o, hconj⟩ :=
    RecipeFieldOmega.ggRawFieldConj_omegaPlus (K := K) (m := 4) (by norm_num) Nat.prime_three
      (by norm_num) hs hna u hu f hf (by rw [← hφ]; exact hφI) (by rw [← hφ]; exact hφ3)
  have hφ' : φ = u' * f' * u'⁻¹ := hφ.trans hconj
  have hf'3 : f' ^ 3 = 1 := hf'o ▸ pow_orderOf_eq_one f'
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h3)
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζo
    norm_num at hζo
  have hζK : (ζ : K) ^ 2 + ζ + 1 = 0 := by
    have h1 : ((ζ : K) - 1) * ((ζ : K) ^ 2 + ζ + 1) = 0 := by
      have : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
      linear_combination this
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (Units.ext (sub_eq_zero.mp h)) hζ1
    · exact h
  have h01 : (1 : Fin 4) ≠ 0 := by decide
  set X : Multiplicative K →* H₈ := (siegelHom (0 : Fin 4) 1).codRestrict H₈
    (fun c => siegelGL_mem_omegaPlus hζ hζ1 h01 _) with hX
  have hXv : ∀ c : K, ((X (Multiplicative.ofAdd c) : H₈) : GL (Fin 4 ⊕ Fin 4) K) =
      siegelGL 0 1 c := fun c => rfl
  have hfX : ∀ c : K,
      f' (π₈ (X (Multiplicative.ofAdd c))) = π₈ (X (Multiplicative.ofAdd (σ c))) :=
    fun c => hσ _ _ (by beta_reduce; rw [hXv, hXv, coe_siegelGL, coe_siegelGL, siegelMat_map])
  have hσ3 : ∀ c : K, σ (σ (σ c)) = c := by
    intro c
    have h := congrArg (fun g : MulAut (LargeEvenProj H₈) => g (π₈ (X (Multiplicative.ofAdd c))))
      hf'3
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h
    rw [hfX, hfX, hfX] at h
    have hm : ((X (Multiplicative.ofAdd (σ (σ (σ c)))))⁻¹ * X (Multiplicative.ofAdd c) : H₈) ∈
        (LargeEvenScalars (Fin 4 ⊕ Fin 4) K).subgroupOf H₈ := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hXv, hXv, siegelGL_inv,
      siegelGL_mul] at hm
    have := eq_zero_of_siegelGL_mem_scalars h01 hm
    linear_combination -this
  have hσζ : σ (ζ : K) = ζ := map_eq_of_cube σ hζK (hσ3 ζ)

  have hodd : Odd 3 := by decide
  set τ : (Fin 4 → Multiplicative (ZMod 3)) →* H₈ := (spTorusGL hζ).codRestrict H₈
    (fun v => spTorusGL_mem_omegaPlus hζ hodd v) with hτ
  have hτv : ∀ v, ((τ v : H₈) : GL (Fin 4 ⊕ Fin 4) K) = spTorusGL hζ v := fun v => rfl
  have hfτ : ∀ v, f' (π₈ (τ v)) = π₈ (τ v) := fun v =>
    hσ _ _ (by beta_reduce; rw [hτv, spTorusGL_map σ hζ hσζ])
  have hinj : Function.Injective ((π₈).comp τ) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv' : ((τ v : H₈) : LargeEvenProj H₈) = 1 := hv
    have hm := (QuotientGroup.eq_one_iff (τ v)).mp hv'
    rw [Subgroup.mem_subgroupOf, hτv] at hm
    exact eq_one_of_spTorusGL_mem_scalars hζ hζo hodd hm
  have hE0card : Nat.card ((π₈).comp τ).range = 81 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun, Nat.card_fin,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3), Nat.card_zmod]
    norm_num
  have hE0 : IsElemAbelian 3 ((π₈).comp τ).range :=
    isElemAbelian_range_of_comm (fun a b => mul_comm a b) (fun a => pow_card_eq_one_zmod a) _
  have hfE : ∀ e ∈ ((π₈).comp τ).range, f' e = e := by
    rintro _ ⟨v, rfl⟩
    exact hfτ v
  have hW02 : IsPGroup 2 ((π₈).comp X).range := by
    rintro ⟨_, c, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← map_pow, Subgroup.coe_one]
    have hc2 : c ^ 2 = 1 := by
      rw [← ofAdd_toAdd c, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]
    rw [hc2, map_one]
  have hW01 : ((π₈).comp X).range ≠ ⊥ := by
    intro hbot
    have hmem : ((π₈).comp X) (Multiplicative.ofAdd 1) ∈ ((π₈).comp X).range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hmem' : ((X (Multiplicative.ofAdd 1) : H₈) : LargeEvenProj H₈) = 1 := hmem
    have hm := (QuotientGroup.eq_one_iff _).mp hmem'
    rw [Subgroup.mem_subgroupOf, hXv] at hm
    exact one_ne_zero (eq_zero_of_siegelGL_mem_scalars h01 hm)
  have hfW : ∀ w ∈ ((π₈).comp X).range, f' w ∈ ((π₈).comp X).range := by
    rintro _ ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd (σ (Multiplicative.toAdd c)), (hfX (Multiplicative.toAdd c)).symm⟩
  have hnorm : ∀ e ∈ ((π₈).comp τ).range, ∀ w ∈ ((π₈).comp X).range,
      e * w * e⁻¹ ∈ ((π₈).comp X).range := by
    rintro _ ⟨v, rfl⟩ _ ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd ((zmodPowHom hζ (v 0) : K) * (zmodPowHom hζ (v 1) : K) *
      Multiplicative.toAdd c), ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hτv]
    change siegelHom (0 : Fin 4) 1 _ = spTorusGL hζ v * siegelHom (0 : Fin 4) 1 c *
      (spTorusGL hζ v)⁻¹
    rw [spTorusGL_apply, siegelHom_apply, siegelHom_apply, diagGL_pairedUnits_conj_siegelGL,
      toAdd_ofAdd]
  refine ⟨((π₈).comp τ).range.map u'.toMonoidHom, ((π₈).comp X).range.map u'.toMonoidHom,
    TableB.isElemAbelian_map hE0 _, ?_, ?_, hW02.map _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective u'.injective, hE0card]
  · rintro _ ⟨e, he, rfl⟩
    rw [hφ']
    change u' (f' (u'⁻¹ (u' e))) = u' e
    rw [MulAut.inv_apply_self, hfE e he]
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ u'.injective]
    exact hW01
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨f' w, hfW w hw, ?_⟩
    rw [hφ']
    change u' (f' w) = u' (f' (u'⁻¹ (u' w)))
    rw [MulAut.inv_apply_self]
  · rintro _ ⟨e, he, rfl⟩ _ ⟨w, hw, rfl⟩
    refine ⟨e * w * e⁻¹, hnorm e he w hw, ?_⟩
    change u' (e * w * e⁻¹) = u' e * u' w * (u' e)⁻¹
    rw [map_mul, map_mul, map_inv]

end Main

end NbrGraphD4Torus

theorem largeEvenLabelAll_d4FieldFixTorus {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : lab.rank = 4) (hev : Even lab.n) : LargeEvenLabelAll lab GGD4FieldFixTorus := by
  have h3 : 3 ∣ 2 ^ lab.n - 1 := by
    obtain ⟨k, hk⟩ := hev
    have h := Nat.sub_dvd_pow_sub_pow 4 1 k
    rw [one_pow, show (4 : ℕ) - 1 = 3 by norm_num,
      show (4 : ℕ) ^ k = 2 ^ (k + k) by rw [← two_mul, pow_mul]; norm_num] at h
    rw [hk]
    exact h
  refine largeEvenLabelAll_omegaPlus ht (by omega) fun K _ _ _ hK => ?_
  rw [h4]
  exact NbrGraphD4Torus.ggD4FieldFixTorus_omegaPlus (by rw [hK]; exact h3)

end CFSG.StandardType
