module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoDef
public import CFSG.Open.StatedZModTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleGraph
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open CFSG.ClassicalInvolution.Upgrade (map_statedOmega statedQuadPlus_comp)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open scoped Matrix

private noncomputable def s16k_piCongrMulEquiv {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (e : K₁ ≃+* K₂) (ι : Type) : Multiplicative (ι → K₁) ≃* Multiplicative (ι → K₂) :=
  (AddEquiv.piCongrRight fun _ : ι => e.toAddEquiv).toMultiplicative

private def s16k_vecMap {K L : Type} {ι : Type} (e : K → L) (v : ι → K) : ι → L :=
  fun i => e (v i)

private theorem s16k_piCongrMulEquiv_toAdd {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (e : K₁ ≃+* K₂) {ι : Type} (x : Multiplicative (ι → K₁)) :
    (s16k_piCongrMulEquiv e ι x).toAdd = s16k_vecMap (⇑e) x.toAdd := rfl

private theorem s16k_vecMap_mulVec {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι]
    (e : K ≃+* L) (M : Matrix ι ι K) (v : ι → K) :
    s16k_vecMap (⇑e) (M *ᵥ v) = (M.map e) *ᵥ (s16k_vecMap (⇑e) v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, s16k_vecMap, Matrix.map_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul]

private noncomputable def s16k_glActMulEquiv {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : GL ι K) :
    Multiplicative (ι → K) ≃* Multiplicative (ι → K) :=
  (Matrix.toLinearEquiv' (M : Matrix ι ι K) (Units.invertible M)).toAddEquiv.toMultiplicative

private theorem s16k_glActMulEquiv_apply {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : GL ι K) (x : Multiplicative (ι → K)) :
    (s16k_glActMulEquiv M x).toAdd = (M : Matrix ι ι K) *ᵥ x.toAdd := by
  change ((Matrix.toLinearEquiv' (M : Matrix ι ι K) (Units.invertible M) :
    Module.End K (ι → K)) : (ι → K) → (ι → K)) x.toAdd = _
  rw [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]

private noncomputable def s16k_vecConjMulEquiv {K₁ K₂ : Type} [Field K₁] [Field K₂] {ι : Type}
    [Fintype ι] [DecidableEq ι] (e : K₁ ≃+* K₂) (M : GL ι K₁) :
    Multiplicative (ι → K₁) ≃* Multiplicative (ι → K₂) :=
  (s16k_glActMulEquiv M).trans (s16k_piCongrMulEquiv e ι)

private theorem s16k_vecConjMulEquiv_apply_toAdd {K₁ K₂ : Type} [Field K₁] [Field K₂] {ι : Type}
    [Fintype ι] [DecidableEq ι] (e : K₁ ≃+* K₂) (M : GL ι K₁)
    (x : Multiplicative (ι → K₁)) :
    (s16k_vecConjMulEquiv e M x).toAdd =
      (M : Matrix ι ι K₁).map e *ᵥ s16k_vecMap (⇑e) x.toAdd := by
  rw [s16k_vecConjMulEquiv, MulEquiv.trans_apply, s16k_piCongrMulEquiv_toAdd,
    s16k_glActMulEquiv_apply, s16k_vecMap_mulVec]

private theorem s16k_natAct_toAdd {K : Type} [Field K] {m : ℕ}
    (g : ↥(StatedOmega (StatedQuadPlus m K)))
    (x : Multiplicative (Fin m ⊕ Fin m → K)) :
    (natAct (StatedOmega (StatedQuadPlus m K)) g x).toAdd =
      (((g : GL (Fin m ⊕ Fin m) K)) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x.toAdd := rfl

private noncomputable def s16k_statedOmegaPlusCongr {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) (m : ℕ) :
    ↥(StatedOmega (StatedQuadPlus m K)) ≃* ↥(StatedOmega (StatedQuadPlus m L)) :=
  ((glCongr (ι := Fin m ⊕ Fin m) e).subgroupMap (StatedOmega (StatedQuadPlus m K))).trans
    (MulEquiv.subgroupCongr (map_statedOmega e (statedQuadPlus_comp e)))

private theorem s16k_statedOmegaPlusCongr_apply_coe {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) (m : ℕ) (x : ↥(StatedOmega (StatedQuadPlus m K))) :
    ((s16k_statedOmegaPlusCongr e m x : ↥(StatedOmega (StatedQuadPlus m L))) :
        GL (Fin m ⊕ Fin m) L) = glCongr e (x : GL (Fin m ⊕ Fin m) K) := by
  simp only [s16k_statedOmegaPlusCongr, MulEquiv.trans_apply, MulEquiv.coe_subgroupMap_apply,
    MulEquiv.subgroupCongr_apply]
  rfl

private noncomputable def s16k_statedOmegaPlusProjEquiv {K : Type} [Field K]
    (hK : Nat.card K = 2) (m : ℕ) :
    ↥(StatedOmega (StatedQuadPlus m K)) ≃* StatedProj (StatedOmega (StatedQuadPlus m K)) :=
  let hsub : (StatedScalars (Fin m ⊕ Fin m) K).subgroupOf
      (StatedOmega (StatedQuadPlus m K)) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK, Subgroup.bot_subgroupOf]
  (QuotientGroup.quotientBot (G := ↥(StatedOmega (StatedQuadPlus m K)))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hsub.symm)

private theorem s16k_statedOmegaPlusProjEquiv_apply_mk {K : Type} [Field K]
    (hK : Nat.card K = 2) (m : ℕ) (x : ↥(StatedOmega (StatedQuadPlus m K))) :
    s16k_statedOmegaPlusProjEquiv hK m x = QuotientGroup.mk x := by
  simp [s16k_statedOmegaPlusProjEquiv]

private theorem s16k_omegaPlus_module_equiv {K₁ K₂ : Type} [Field K₁] [Field K₂]
    [Finite K₁] [Finite K₂] (h₁ : Nat.card K₁ = 2) (h₂ : Nat.card K₂ = 2)
    {m : ℕ} (hm : 5 ≤ m)
    (φ : ↥(StatedOmega (StatedQuadPlus m K₁)) ≃* ↥(StatedOmega (StatedQuadPlus m K₂))) :
    ∃ A : Multiplicative (Fin m ⊕ Fin m → K₁) ≃* Multiplicative (Fin m ⊕ Fin m → K₂),
      ∀ (γ : ↥(StatedOmega (StatedQuadPlus m K₁)))
        (x : Multiplicative (Fin m ⊕ Fin m → K₁)),
        A (natAct (StatedOmega (StatedQuadPlus m K₁)) γ x) =
          natAct (StatedOmega (StatedQuadPlus m K₂)) (φ γ) (A x) := by
  haveI : Fintype K₁ := Fintype.ofFinite K₁
  haveI : Fintype K₂ := Fintype.ofFinite K₂
  let e : K₁ ≃+* K₂ := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h₁, h₂])
  let E : ↥(StatedOmega (StatedQuadPlus m K₁)) ≃* ↥(StatedOmega (StatedQuadPlus m K₂)) :=
    s16k_statedOmegaPlusCongr e m
  let ψ : ↥(StatedOmega (StatedQuadPlus m K₁)) ≃* ↥(StatedOmega (StatedQuadPlus m K₁)) :=
    φ.trans E.symm
  let j : ↥(StatedOmega (StatedQuadPlus m K₁)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus m K₁)) :=
    s16k_statedOmegaPlusProjEquiv h₁ m
  let β : MulAut (StatedProj (StatedOmega (StatedQuadPlus m K₁))) :=
    { toFun := fun q => j (ψ (j.symm q))
      invFun := fun q => j (ψ.symm (j.symm q))
      left_inv := fun q => by simp
      right_inv := fun q => by simp
      map_mul' := fun q r => by simp [map_mul] }
  have hβj : ∀ x, β (j x) = j (ψ x) := by intro x; simp [β]
  obtain ⟨σ, A, μ, hμ, hAQ, hβ⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.exists_semilinear_plus (n := m) hm β
  have hσ : σ = (1 : K₁ ≃+* K₁) :=
    CFSG.ComponentClassification.OutcomeLocal.ringEquiv_eq_one_of_card_two h₁ σ
  have hglAut : ∀ g : GL (Fin m ⊕ Fin m) K₁, glAut σ g = g := by
    intro g
    rw [hσ]
    exact congrArg (fun (φ : MulAut (GL (Fin m ⊕ Fin m) K₁)) => φ g) (map_one glAut)
  have hψg : ∀ g : ↥(StatedOmega (StatedQuadPlus m K₁)),
      ∃ hg : A * glAut σ (g : GL (Fin m ⊕ Fin m) K₁) * A⁻¹ ∈
        StatedOmega (StatedQuadPlus m K₁),
        ψ g = ⟨A * glAut σ (g : GL (Fin m ⊕ Fin m) K₁) * A⁻¹, hg⟩ := by
    intro g
    obtain ⟨hg, hβg⟩ := hβ g
    refine ⟨hg, ?_⟩
    apply j.injective
    rw [← hβj g, s16k_statedOmegaPlusProjEquiv_apply_mk h₁ m g, hβg,
      s16k_statedOmegaPlusProjEquiv_apply_mk h₁ m ⟨_, hg⟩]
  have hφg : ∀ g : ↥(StatedOmega (StatedQuadPlus m K₁)),
      (φ g : GL (Fin m ⊕ Fin m) K₂) =
        glCongr e (A * (g : GL (Fin m ⊕ Fin m) K₁) * A⁻¹) := by
    intro g
    obtain ⟨hg, hψg'⟩ := hψg g
    have hE : E (ψ g) = φ g := by
      show E ((φ.trans E.symm) g) = φ g
      rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h1 : E (⟨A * glAut σ (g : GL (Fin m ⊕ Fin m) K₁) * A⁻¹, hg⟩) = φ g := by
      rw [← hψg']
      exact hE
    have h2 : glCongr e (A * glAut σ (g : GL (Fin m ⊕ Fin m) K₁) * A⁻¹) =
        (φ g : GL (Fin m ⊕ Fin m) K₂) := by
      have h3 := congrArg (fun z : ↥(StatedOmega (StatedQuadPlus m K₂)) =>
        (z : GL (Fin m ⊕ Fin m) K₂)) h1
      rwa [s16k_statedOmegaPlusCongr_apply_coe] at h3
    rw [← h2, hglAut]
  have hmat : ∀ g : ↥(StatedOmega (StatedQuadPlus m K₁)),
      (((φ g : GL (Fin m ⊕ Fin m) K₂)) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₂) *
          (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁).map e =
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁).map e *
          (((g : GL (Fin m ⊕ Fin m) K₁)) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁).map e := by
    intro g
    have hGL : (φ g : GL (Fin m ⊕ Fin m) K₂) * glCongr e A =
        glCongr e A * glCongr e (g : GL (Fin m ⊕ Fin m) K₁) := by
      rw [hφg g, ← map_mul, ← map_mul]
      congr 1
      group
    have h4 := congrArg (fun u : GL (Fin m ⊕ Fin m) K₂ =>
      (u : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₂)) hGL
    simpa [glCongr_coe, Units.val_mul] using h4
  refine ⟨s16k_vecConjMulEquiv e A, ?_⟩
  intro g x
  apply Multiplicative.toAdd.injective
  rw [s16k_vecConjMulEquiv_apply_toAdd, s16k_natAct_toAdd, s16k_vecMap_mulVec,
    Matrix.mulVec_mulVec]
  conv_rhs => rw [s16k_natAct_toAdd, s16k_vecConjMulEquiv_apply_toAdd, Matrix.mulVec_mulVec]
  rw [hmat g]

theorem s16k_omegaPlus_two_equiv {n : ℕ} (hn : 8 ≤ n) {X : Type} [Group X] [Finite X]
    (hX : IsOmegaPlus X n 1) {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
    (h₁ : Nat.card K₁ = 2) (h₂ : Nat.card K₂ = 2)
    {π₁ : ↥(StatedOmega (StatedQuadPlus (n / 2) K₁)) →* X}
    {π₂ : ↥(StatedOmega (StatedQuadPlus (n / 2) K₂)) →* X} (hπ₁ : Function.Surjective π₁)
    (hπ₂ : Function.Surjective π₂) :
    Function.Injective π₁ ∧ Function.Injective π₂ ∧
      (10 ≤ n → S16kModelsEquivVia (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K₁)))
        (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K₁))).act
        (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K₂))) π₁ π₂) := by
  classical
  obtain ⟨-, K', hK'field, hK'fin, hK'card, ⟨eX⟩⟩ := hX
  letI : Field K' := hK'field
  letI : Finite K' := hK'fin
  haveI : Fintype K₁ := Fintype.ofFinite K₁
  haveI : Fintype K₂ := Fintype.ofFinite K₂
  haveI : Fintype K' := Fintype.ofFinite K'
  have hK' : Nat.card K' = 2 := by simpa using hK'card
  have hcardX : Nat.card X =
      Nat.card (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K'))) :=
    Nat.card_congr eX.toEquiv
  let e₁ : K₁ ≃+* K' := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h₁, hK'])
  have hcard₁ : Nat.card ↥(StatedOmega (StatedQuadPlus (n / 2) K₁)) = Nat.card X := by
    rw [Nat.card_congr (s16k_statedOmegaPlusCongr e₁ (n / 2)).toEquiv,
      Nat.card_congr (s16k_statedOmegaPlusProjEquiv hK' (n / 2)).toEquiv]
    exact hcardX.symm
  have hinj₁ : Function.Injective π₁ :=
    (Function.Surjective.bijective_of_nat_card_le hπ₁ (le_of_eq hcard₁)).1
  let e₂ : K₂ ≃+* K' := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h₂, hK'])
  have hcard₂ : Nat.card ↥(StatedOmega (StatedQuadPlus (n / 2) K₂)) = Nat.card X := by
    rw [Nat.card_congr (s16k_statedOmegaPlusCongr e₂ (n / 2)).toEquiv,
      Nat.card_congr (s16k_statedOmegaPlusProjEquiv hK' (n / 2)).toEquiv]
    exact hcardX.symm
  have hinj₂ : Function.Injective π₂ :=
    (Function.Surjective.bijective_of_nat_card_le hπ₂ (le_of_eq hcard₂)).1
  refine ⟨hinj₁, hinj₂, fun h10 => ?_⟩
  have hm : 5 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  let π₁e : ↥(StatedOmega (StatedQuadPlus (n / 2) K₁)) ≃* X :=
    MulEquiv.ofBijective π₁ ⟨hinj₁, hπ₁⟩
  let π₂e : ↥(StatedOmega (StatedQuadPlus (n / 2) K₂)) ≃* X :=
    MulEquiv.ofBijective π₂ ⟨hinj₂, hπ₂⟩
  let φ : ↥(StatedOmega (StatedQuadPlus (n / 2) K₁)) ≃*
      ↥(StatedOmega (StatedQuadPlus (n / 2) K₂)) := π₁e.trans π₂e.symm
  obtain ⟨A, hA⟩ := s16k_omegaPlus_module_equiv h₁ h₂ hm φ
  refine ⟨A, ?_, ?_, ?_⟩
  · intro m
    exact iff_of_true (Subgroup.mem_top m) (Subgroup.mem_top (A m))
  · intro m
    exact (Subgroup.mem_bot).trans
      ((MulEquiv.map_eq_one_iff A).symm.trans (Subgroup.mem_bot).symm)
  · intro γ₁ γ₂ hγ m
    have hφ : φ γ₁ = γ₂ := by
      have h1 : π₁e γ₁ = π₂e (show ↥(StatedOmega (StatedQuadPlus (n / 2) K₂)) from γ₂) := by
        change π₁ γ₁ = π₂ γ₂
        exact hγ
      show π₂e.symm (π₁e γ₁) = γ₂
      rw [h1, MulEquiv.symm_apply_apply]
    show A (natAct (StatedOmega (StatedQuadPlus (n / 2) K₁)) γ₁ m) =
      natAct (StatedOmega (StatedQuadPlus (n / 2) K₂)) γ₂ (A m)
    rw [← hφ]
    exact hA γ₁ m

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
