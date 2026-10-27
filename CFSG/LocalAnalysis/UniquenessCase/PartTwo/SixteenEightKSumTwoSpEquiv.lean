module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoDef
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSpAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (congr_conj)
open CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped Matrix

private noncomputable def s16k_piCongrMulEquiv {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (e : K₁ ≃+* K₂) (ι : Type) : Multiplicative (ι → K₁) ≃* Multiplicative (ι → K₂) :=
  (AddEquiv.piCongrRight fun _ : ι => e.toAddEquiv).toMultiplicative

private theorem s16k_piCongrMulEquiv_toAdd {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (e : K₁ ≃+* K₂) {ι : Type} (x : Multiplicative (ι → K₁)) :
    (s16k_piCongrMulEquiv e ι x).toAdd = fun i => e (x.toAdd i) := rfl

private noncomputable def s16k_spMapEquiv {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (e : K₁ ≃+* K₂) (m : ℕ) : StatedSp m K₁ ≃* StatedSp m K₂ :=
  MulEquiv.ofBijective (spMap (n := m) e.toRingHom)
    ⟨spMap_injective e.toRingHom, spMap_surjective e⟩

private noncomputable def s16k_mulVecAddEquiv {K : Type} [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] (M : GL ι K) : (ι → K) ≃+ (ι → K) :=
  (Matrix.toLinearEquiv' (M : Matrix ι ι K) (Units.invertible M)).toAddEquiv

private theorem s16k_mulVecAddEquiv_apply {K : Type} [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] (M : GL ι K) (v : ι → K) :
    s16k_mulVecAddEquiv M v = (M : Matrix ι ι K) *ᵥ v := by
  change ((Matrix.toLinearEquiv' (M : Matrix ι ι K) (Units.invertible M) :
    Module.End K (ι → K)) : (ι → K) → (ι → K)) v = (M : Matrix ι ι K) *ᵥ v
  rw [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]

private noncomputable def s16k_mulVecMulEquiv {K : Type} [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] (M : GL ι K) :
    Multiplicative (ι → K) ≃* Multiplicative (ι → K) :=
  (s16k_mulVecAddEquiv M).toMultiplicative

private theorem s16k_mulVecMulEquiv_apply {K : Type} [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] (M : GL ι K) (x : Multiplicative (ι → K)) :
    s16k_mulVecMulEquiv M x = Multiplicative.ofAdd ((M : Matrix ι ι K) *ᵥ x.toAdd) := by
  change Multiplicative.ofAdd (s16k_mulVecAddEquiv M x.toAdd) =
    Multiplicative.ofAdd ((M : Matrix ι ι K) *ᵥ x.toAdd)
  rw [s16k_mulVecAddEquiv_apply]

private theorem s16k_natAct_toAdd {K : Type} [Field K] {m : ℕ}
    (g : StatedSp m K) (x : Multiplicative (Fin m ⊕ Fin m → K)) :
    (natAct (StatedSp m K) g x).toAdd = mat m K g *ᵥ x.toAdd := rfl

private theorem s16k_spMapEquiv_natAct {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (e : K₁ ≃+* K₂) {m : ℕ} (γ : StatedSp m K₁)
    (x : Multiplicative (Fin m ⊕ Fin m → K₁)) :
    s16k_piCongrMulEquiv e (Fin m ⊕ Fin m) (natAct (StatedSp m K₁) γ x) =
      natAct (StatedSp m K₂) (s16k_spMapEquiv e m γ)
        (s16k_piCongrMulEquiv e (Fin m ⊕ Fin m) x) := by
  apply Multiplicative.toAdd.injective
  rw [s16k_piCongrMulEquiv_toAdd, s16k_natAct_toAdd, s16k_natAct_toAdd,
    s16k_piCongrMulEquiv_toAdd]
  change (fun i => e ((mat m K₁ γ *ᵥ x.toAdd) i)) =
    mat m K₂ (spMap (n := m) e.toRingHom γ) *ᵥ (fun i => e (x.toAdd i))
  rw [mat_spMap]
  ext i
  exact RingHom.map_mulVec e.toRingHom (mat m K₁ γ) x.toAdd i

private theorem s16k_statedSp_aut_eq_conj {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) (ψ : StatedSp m K ≃* StatedSp m K) :
    ∃ M : StatedSp m K, ψ = MulAut.conj M := by
  haveI : Fintype K := Fintype.ofFinite K
  have hunits : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  haveI : Subsingleton Kˣ := Finite.card_le_one_iff_subsingleton.mp (le_of_eq hunits)
  have hscal : StatedScalars (Fin m ⊕ Fin m) K = ⊥ := by
    unfold StatedScalars
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨u, rfl⟩
    rw [Subsingleton.elim u 1, map_one]
  have hsub : (StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (StatedSp m K) = ⊥ := by
    rw [hscal, Subgroup.bot_subgroupOf]
  let j : ↥(StatedSp m K) ≃* StatedProj (StatedSp m K) :=
    (QuotientGroup.quotientBot (G := ↥(StatedSp m K))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hsub.symm)
  obtain ⟨g, hg⟩ :=
    CFSG.SeitzReduction.SporadicRefine.allInner_statedProjSp_of_card_two (r := m) hm hK
      (MulAut.congr j ψ)
  refine ⟨j.symm g, ?_⟩
  rw [← congr_conj j.symm g, ← hg]
  ext x
  simp [MulAut.congr, MulEquiv.trans_apply]

private theorem s16k_sp_module_equiv {K₁ K₂ : Type} [Field K₁] [Field K₂]
    [Finite K₁] [Finite K₂] (h₁ : Nat.card K₁ = 2) (h₂ : Nat.card K₂ = 2)
    {m : ℕ} (hm : 3 ≤ m) (φ : StatedSp m K₁ ≃* StatedSp m K₂) :
    ∃ A : Multiplicative (Fin m ⊕ Fin m → K₁) ≃* Multiplicative (Fin m ⊕ Fin m → K₂),
      ∀ (γ : StatedSp m K₁) (x : Multiplicative (Fin m ⊕ Fin m → K₁)),
        A (natAct (StatedSp m K₁) γ x) = natAct (StatedSp m K₂) (φ γ) (A x) := by
  haveI : Fintype K₁ := Fintype.ofFinite K₁
  haveI : Fintype K₂ := Fintype.ofFinite K₂
  let e : K₁ ≃+* K₂ := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h₁, h₂])
  obtain ⟨M, hM⟩ :=
    s16k_statedSp_aut_eq_conj h₁ hm (φ.trans (s16k_spMapEquiv e m).symm)
  let E := s16k_piCongrMulEquiv e (Fin m ⊕ Fin m)
  let B := s16k_mulVecMulEquiv (K := K₁) (M : GL (Fin m ⊕ Fin m) K₁)
  refine ⟨B.trans E, ?_⟩
  intro γ x
  have hφγ : φ γ = s16k_spMapEquiv e m (M * γ * M⁻¹) := by
    have h := congrArg (fun (f : StatedSp m K₁ ≃* StatedSp m K₁) => f γ) hM
    simp only [MulEquiv.trans_apply, MulAut.conj_apply] at h
    rw [← h, MulEquiv.apply_symm_apply]
  change E (B (natAct (StatedSp m K₁) γ x)) =
    natAct (StatedSp m K₂) (φ γ) (E (B x))
  rw [hφγ]
  change E (B (natAct (StatedSp m K₁) γ x)) =
    natAct (StatedSp m K₂) (s16k_spMapEquiv e m (M * γ * M⁻¹)) (E (B x))
  rw [← s16k_spMapEquiv_natAct e (M * γ * M⁻¹) (B x)]
  change E (B (natAct (StatedSp m K₁) γ x)) =
    E (natAct (StatedSp m K₁) (M * γ * M⁻¹) (B x))
  rw [MulEquiv.apply_eq_iff_eq]
  apply Multiplicative.toAdd.injective
  change (s16k_mulVecMulEquiv (M : GL (Fin m ⊕ Fin m) K₁)
      (natAct (StatedSp m K₁) γ x)).toAdd =
    (natAct (StatedSp m K₁) (M * γ * M⁻¹)
      (s16k_mulVecMulEquiv (M : GL (Fin m ⊕ Fin m) K₁) x)).toAdd
  simp only [s16k_mulVecMulEquiv_apply, s16k_natAct_toAdd, toAdd_ofAdd,
    Matrix.mulVec_mulVec]
  change (mat m K₁ M * mat m K₁ γ) *ᵥ x.toAdd =
    (mat m K₁ (M * γ * M⁻¹) * mat m K₁ M) *ᵥ x.toAdd
  have hmat : mat m K₁ (M * γ * M⁻¹) * mat m K₁ M = mat m K₁ M * mat m K₁ γ := by
    rw [← map_mul (mat m K₁), ← map_mul (mat m K₁),
      show (M * γ * M⁻¹) * M = M * γ from by group]
  rw [hmat]

theorem s16k_sp_two_equiv {n : ℕ} (hn : 8 ≤ n) {X : Type} [Group X] [Finite X]
    (hX : IsSpn X n 1) {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
    (h₁ : Nat.card K₁ = 2) (h₂ : Nat.card K₂ = 2) {π₁ : ↥(StatedSp (n / 2) K₁) →* X}
    {π₂ : ↥(StatedSp (n / 2) K₂) →* X} (hπ₁ : Function.Surjective π₁)
    (hπ₂ : Function.Surjective π₂) :
    Function.Injective π₁ ∧ Function.Injective π₂ ∧
      S16kModelsEquivVia (FFModel.nat (StatedSp (n / 2) K₁)) (FFModel.nat (StatedSp (n / 2) K₁)).act
        (FFModel.nat (StatedSp (n / 2) K₂)) π₁ π₂ := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eX⟩⟩ := hX
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype K₁ := Fintype.ofFinite K₁
  haveI : Fintype K₂ := Fintype.ofFinite K₂
  have hm : 3 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hcardX : Nat.card X = Nat.card (StatedSp (n / 2) K) := Nat.card_congr eX.toEquiv
  let e₁ : K₁ ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h₁, hKcard]
    norm_num)
  have hcard₁ : Nat.card (StatedSp (n / 2) K₁) = Nat.card X := by
    rw [Nat.card_congr (s16k_spMapEquiv e₁ (n / 2)).toEquiv, ← hcardX]
  have hinj₁ : Function.Injective π₁ :=
    (Function.Surjective.bijective_of_nat_card_le hπ₁ (le_of_eq hcard₁)).1
  let e₂ : K₂ ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h₂, hKcard]
    norm_num)
  have hcard₂ : Nat.card (StatedSp (n / 2) K₂) = Nat.card X := by
    rw [Nat.card_congr (s16k_spMapEquiv e₂ (n / 2)).toEquiv, ← hcardX]
  have hinj₂ : Function.Injective π₂ :=
    (Function.Surjective.bijective_of_nat_card_le hπ₂ (le_of_eq hcard₂)).1
  let π₁e : StatedSp (n / 2) K₁ ≃* X := MulEquiv.ofBijective π₁ ⟨hinj₁, hπ₁⟩
  let π₂e : StatedSp (n / 2) K₂ ≃* X := MulEquiv.ofBijective π₂ ⟨hinj₂, hπ₂⟩
  let φ : StatedSp (n / 2) K₁ ≃* StatedSp (n / 2) K₂ := π₁e.trans π₂e.symm
  obtain ⟨A, hA⟩ := s16k_sp_module_equiv h₁ h₂ hm φ
  refine ⟨hinj₁, hinj₂, A, ?_, ?_, ?_⟩
  · intro m
    exact iff_of_true (Subgroup.mem_top m) (Subgroup.mem_top (A m))
  · intro m
    exact (Subgroup.mem_bot).trans
      ((MulEquiv.map_eq_one_iff A).symm.trans (Subgroup.mem_bot).symm)
  · intro γ₁ γ₂ hγ m
    have hφ : φ γ₁ = γ₂ := by
      have h1 : π₁e γ₁ = π₂e (show ↥(StatedSp (n / 2) K₂) from γ₂) := by
        change π₁ γ₁ = π₂ γ₂
        exact hγ
      show π₂e.symm (π₁e γ₁) = γ₂
      rw [h1, MulEquiv.symm_apply_apply]
    show A (natAct (StatedSp (n / 2) K₁) γ₁ m) =
      natAct (StatedSp (n / 2) K₂) γ₂ (A m)
    rw [← hφ]
    exact hA γ₁ m

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
