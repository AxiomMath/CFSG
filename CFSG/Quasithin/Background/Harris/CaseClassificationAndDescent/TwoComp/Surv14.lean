module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.TensorData
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.TensorAssemble
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.CoverEquiv
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.OddL2Rank
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Toolkit

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
  CFSG.Assembly.LowTwoRank
open scoped TensorProduct Matrix

section LinGrp

variable {F : Type} [Field F] [Finite F] {W : Type} [AddCommGroup W] [Module F W]
  [Module.Finite F W]

theorem natCard_linearEquiv :
    Nat.card (W ≃ₗ[F] W) = ∏ i : Fin (Module.finrank F W),
      (Nat.card F ^ Module.finrank F W - Nat.card F ^ (i : ℕ)) := by
  have e : (W ≃ₗ[F] W) ≃* Matrix.GeneralLinearGroup (Fin (Module.finrank F W)) F :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F W).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis F W)).toMulEquiv)
  have := Fintype.ofFinite F
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, Nat.card_eq_fintype_card (α := F)]

theorem card_dvd_prod_of_injective {G : Type} [Group G] (ρ : G →* (W ≃ₗ[F] W))
    (hρ : Function.Injective ρ) :
    Nat.card G ∣ ∏ i : Fin (Module.finrank F W),
      (Nat.card F ^ Module.finrank F W - Nat.card F ^ (i : ℕ)) := by
  rw [← natCard_linearEquiv]
  exact Subgroup.card_dvd_of_injective ρ hρ

end LinGrp

theorem numerics_gl {e k t : ℕ} (he : 1 ≤ e) (hk : 1 ≤ k) (ht : 1 ≤ t) (hkt : e * k * t ≤ 10)
    (h₀ : 168 ∣ ∏ i : Fin k, ((2 ^ e) ^ k - (2 ^ e) ^ (i : ℕ)))
    (h₁ : 168 ∣ ∏ i : Fin t, ((2 ^ e) ^ t - (2 ^ e) ^ (i : ℕ))) :
    e = 1 ∧ k = 3 ∧ t = 3 := by
  have he10 : e ≤ 10 := le_trans (by simpa using Nat.mul_le_mul (Nat.mul_le_mul (le_refl e) hk) ht)
    hkt
  have hk10 : k ≤ 10 := le_trans (by simpa using Nat.mul_le_mul (Nat.mul_le_mul he (le_refl k)) ht)
    hkt
  have ht10 : t ≤ 10 := le_trans (by simpa using Nat.mul_le_mul (Nat.mul_le_mul he hk) (le_refl t))
    hkt
  interval_cases e <;> interval_cases k <;> (try omega) <;> interval_cases t <;> (try omega) <;>
    first
    | exact ⟨rfl, rfl, rfl⟩
    | (exfalso; simp [Fin.prod_univ_succ] at h₀ h₁)

section Group

theorem center_eq_bot_of_psl_seven {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (hS : IsPSL 2 7 1 (L ⧸ Subgroup.center L)) :
    Subgroup.center L = ⊥ ∧ Nat.card L = 168 ∧ StatedClassicalModel L .PSL 2 7 1 := by
  have hp7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hadm, K, hF, hfin, hK, ⟨e⟩⟩ := hS
  have hK' : Nat.card K = 7 ^ 1 := hK
  obtain ⟨f, hf⟩ := exists_mulEquiv_of_cover_odd hq hodd e
    (fun E _ _ _ π hs hker hod =>
      (CFSG.SectionRank.OddCover.odd_psl_two_perfect_odd_cover_kernel (p := 7) (f := 1)
        (by norm_num) hK' π hs hker hod).1 (by norm_num))
  refine ⟨?_, ?_, hadm, K, hF, hfin, hK, ⟨f⟩⟩
  · refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    apply f.injective
    rw [hf, (QuotientGroup.eq_one_iff z).2 hz, map_one, map_one]
  · rw [Nat.card_congr f.toEquiv,
      (CFSG.SectionRank.OddCover.odd_psl_two_sylow_data (p := 7) (f := 1) (by norm_num) hK').2.2.1]
    norm_num

end Group

section Tensor

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {V₀ V₁ : Type} [AddCommGroup V₀] [AddCommGroup V₁] [Module F V₀] [Module F V₁]
  [Module.Finite F V₀] [Module.Finite F V₁]

theorem finrank_eq_of_tensor (e : V ≃+ V₀ ⊗[F] V₁) :
    Nat.card F = 2 ^ Module.finrank (ZMod 2) F ∧
      Module.finrank (ZMod 2) V =
        Module.finrank (ZMod 2) F * (Module.finrank F V₀ * Module.finrank F V₁) := by
  have hF : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rwa [Nat.card_zmod] at this
  refine ⟨hF, ?_⟩
  have h1 : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod] at this
  have h2 : Nat.card V = Nat.card F ^ (Module.finrank F V₀ * Module.finrank F V₁) := by
    rw [Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := F) (V := V₀ ⊗[F] V₁),
      Module.finrank_tensorProduct]
  rw [h1, hF, ← pow_mul] at h2
  exact Nat.pow_right_injective (le_refl 2) h2

omit [Finite V] [Finite F] [Algebra (ZMod 2) F] [Module.Finite F V₀] [Module.Finite F V₁] in
theorem injective_rho₀ {L : Subgroup (GLV V)} (ρ₀ : ↥L →* (V₀ ≃ₗ[F] V₀))
    (e : V ≃+ V₀ ⊗[F] V₁)
    (he₀ : ∀ (g : ↥L) (v : V), e ((g : GLV V) v) =
      TensorProduct.map (ρ₀ g : V₀ →ₗ[F] V₀) LinearMap.id (e v)) : Function.Injective ρ₀ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply e.injective
  rw [he₀, hg]
  simp

omit [Finite V] [Finite F] [Algebra (ZMod 2) F] [Module.Finite F V₀] [Module.Finite F V₁] in
theorem injective_rho₁ {L₂ : Subgroup (GLV V)} (ρ₁ : ↥L₂ →* (V₁ ≃ₗ[F] V₁))
    (e : V ≃+ V₀ ⊗[F] V₁)
    (he₁ : ∀ (g : ↥L₂) (v : V), e ((g : GLV V) v) =
      TensorProduct.map LinearMap.id (ρ₁ g : V₁ →ₗ[F] V₁) (e v)) : Function.Injective ρ₁ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply e.injective
  rw [he₁, hg]
  simp

theorem params_of_tensor {L L₂ : Subgroup (GLV V)} (hL₀ : Nat.card ↥L = 168)
    (hL₁ : Nat.card ↥L₂ = 168) [Nontrivial V₀] [Nontrivial V₁]
    (ρ₀ : ↥L →* (V₀ ≃ₗ[F] V₀)) (ρ₁ : ↥L₂ →* (V₁ ≃ₗ[F] V₁)) (e : V ≃+ V₀ ⊗[F] V₁)
    (he₀ : ∀ (g : ↥L) (v : V), e ((g : GLV V) v) =
      TensorProduct.map (ρ₀ g : V₀ →ₗ[F] V₀) LinearMap.id (e v))
    (he₁ : ∀ (g : ↥L₂) (v : V), e ((g : GLV V) v) =
      TensorProduct.map LinearMap.id (ρ₁ g : V₁ →ₗ[F] V₁) (e v))
    (hd : Module.finrank (ZMod 2) V ≤ 10) :
    Nat.card F = 2 ∧ Module.finrank F V₀ = 3 ∧ Module.finrank F V₁ = 3 ∧
      Module.finrank (ZMod 2) V = 9 := by
  obtain ⟨hF, hV⟩ := finrank_eq_of_tensor (V := V) (F := F) e
  have hdv₀ := hL₀ ▸ card_dvd_prod_of_injective ρ₀ (injective_rho₀ ρ₀ e he₀)
  have hdv₁ := hL₁ ▸ card_dvd_prod_of_injective ρ₁ (injective_rho₁ ρ₁ e he₁)
  rw [hF] at hdv₀ hdv₁
  have hk : 1 ≤ Module.finrank F V₀ := Module.finrank_pos
  have ht : 1 ≤ Module.finrank F V₁ := Module.finrank_pos
  have hel : 1 ≤ Module.finrank (ZMod 2) F := by
    by_contra h0
    have h0' : Module.finrank (ZMod 2) F = 0 := by omega
    rw [h0', pow_zero] at hF
    have : Nontrivial F := inferInstance
    have := Finite.one_lt_card (α := F)
    omega
  have hkt : Module.finrank (ZMod 2) F * Module.finrank F V₀ * Module.finrank F V₁ ≤ 10 := by
    rw [mul_assoc, ← hV]; exact hd
  obtain ⟨h1, h2, h3⟩ := numerics_gl hel hk ht hkt hdv₀ hdv₁
  refine ⟨?_, h2, h3, ?_⟩
  · rw [hF, h1]; norm_num
  · rw [hV, h1, h2, h3]

end Tensor

section Transport

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def statedSLEquivOfRingEquiv (d : ℕ) {K K' : Type} [Field K] [Field K']
    (σ : K ≃+* K') : ↥(StatedSL d K) ≃* ↥(StatedSL d K') :=
  (specialLinearGroupEquivStatedSL d K).symm.trans
    ((MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map σ.toRingHom)
      (Matrix.SpecialLinearGroup.map σ.symm.toRingHom) (by ext x i j; simp)
      (by ext x i j; simp)).trans (specialLinearGroupEquivStatedSL d K'))

theorem statedSLEquivOfRingEquiv_coe (d : ℕ) {K K' : Type} [Field K] [Field K']
    (σ : K ≃+* K') (g : ↥(StatedSL d K)) :
    (((statedSLEquivOfRingEquiv d σ g : ↥(StatedSL d K')) :
      Matrix.GeneralLinearGroup (Fin d) K') : Matrix (Fin d) (Fin d) K') =
      ((g : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ := by
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL d K).surjective g
  simp [statedSLEquivOfRingEquiv, specialLinearGroupEquivStatedSL_coe]

@[expose] def matrixMapEquiv (d : ℕ) {K K' : Type} [Field K] [Field K'] [Algebra (ZMod 2) K]
    [Algebra (ZMod 2) K'] (σ : K ≃+* K') :
    Matrix (Fin d) (Fin d) K ≃ₗ[ZMod 2] Matrix (Fin d) (Fin d) K' :=
  { (RingEquiv.mapMatrix (m := Fin d) σ).toAddEquiv with
    map_smul' := fun c M => ZMod.map_smul (RingEquiv.mapMatrix (m := Fin d) σ).toAddMonoidHom c M }

theorem isTensorModel_of_ringEquiv {d : ℕ} {K K' : Type} [Field K] [Field K']
    [Algebra (ZMod 2) K] [Algebra (ZMod 2) K'] (σ : K ≃+* K') {H : Subgroup (GLV V)}
    (h : IsTensorModel d K H) : IsTensorModel d K' H := by
  obtain ⟨φ, ψ, hψ⟩ := h
  refine ⟨φ.trans (MulEquiv.prodCongr (statedSLEquivOfRingEquiv d σ)
    (statedSLEquivOfRingEquiv d σ)), ψ.trans (matrixMapEquiv d σ), fun γ v => ?_⟩
  have e1 := statedSLEquivOfRingEquiv_coe d σ (φ γ).1
  have e2 := statedSLEquivOfRingEquiv_coe d σ (φ γ).2
  change (ψ ((γ : GLV V) v)).map σ =
    ((statedSLEquivOfRingEquiv d σ (φ γ).1 : Matrix.GeneralLinearGroup (Fin d) K') :
      Matrix (Fin d) (Fin d) K') * (ψ v).map σ *
    ((statedSLEquivOfRingEquiv d σ (φ γ).2 : Matrix.GeneralLinearGroup (Fin d) K') :
      Matrix (Fin d) (Fin d) K')ᵀ
  have hmul : ∀ A B : Matrix (Fin d) (Fin d) K, (A * B).map σ = A.map σ * B.map σ :=
    fun A B => map_mul (RingEquiv.mapMatrix (m := Fin d) σ) A B
  rw [hψ γ v, e1, e2, hmul, hmul, Matrix.transpose_map]

end Transport

theorem card_statedSL_three {F : Type} [Field F] [Finite F] (h : Nat.card F = 2) :
    Nat.card ↥(StatedSL 3 F) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two h

section Main

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Γ A L L₂ : Subgroup (GLV V)} {m : ℕ}

theorem Setting.tensor14
    (h : Setting Γ A L L₂ m) (hS : IsPSL 2 7 1 (↥L ⧸ Subgroup.center ↥L)) :
    Module.finrank (ZMod 2) V = 9 ∧ m = 4 ∧ IsTensorModel 3 (ZMod 2) (L ⊔ L₂) := by
  have := h.nontrivial_V
  have hp7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hq : CFSG.Open.IsQuasisimple ↥L := h.hyp.L_comp.2.2
  have hq₂ : CFSG.Open.IsQuasisimple ↥L₂ := h.comp₂.2.2
  obtain ⟨hZ, hcL, hmod⟩ := center_eq_bot_of_psl_seven hq h.centerL_odd hS
  obtain ⟨φ, -⟩ := h.qe
  have hcL₂ : Nat.card ↥L₂ = 168 := by rw [← Nat.card_congr φ.toEquiv]; exact hcL
  have hm : m ≤ 2 * 2 := h.m_le_two_mul (MulEquiv.refl ↥L) (r := 2) (by norm_num)
    (fun B hc h2 => card_elemAbelian_mulAut_of_model_prime (by norm_num) hmod B hc h2)
  obtain ⟨F, _, _, _, V₀, V₁, _, _, _, _, _, _, ρ₀, ρ₁, e, hn₀, hn₁, he₀, he₁, -, -⟩ :=
    exists_tensorData h.comm h.hyp.H_irr
  have hbound := h.hyp.bound
  obtain ⟨hF2, hk, ht, hV9⟩ := params_of_tensor hcL hcL₂ ρ₀ ρ₁ e he₀ he₁ (by omega)
  have hinf : L ⊓ L₂ = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hxc : (⟨x, hx.1⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (h.comm y y.2 x hx.2)
    rw [hZ, Subgroup.mem_bot] at hxc
    exact congrArg Subtype.val hxc
  have : Group.IsPerfect ↥L := ⟨hq.1⟩
  have : Group.IsPerfect ↥L₂ := ⟨hq₂.1⟩
  have hT := isTensorModel_of_tensorData h.comm hinf ρ₀ ρ₁ e he₀ he₁ (d := 3) hk ht
    inferInstance inferInstance (hcL.trans (card_statedSL_three hF2).symm)
    (hcL₂.trans (card_statedSL_three hF2).symm) (injective_rho₀ ρ₀ e he₀)
    (injective_rho₁ ρ₁ e he₁)
  have := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 := by
    rwa [← Nat.card_eq_fintype_card]
  refine ⟨hV9, by omega, ?_⟩
  exact isTensorModel_of_ringEquiv (ZMod.ringEquivOfPrime F Nat.prime_two hFc).symm hT

end Main

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
