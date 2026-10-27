module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoDef
public import CFSG.RankThree.PartOne.TAIL.LSideOutAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.KFacts.K71Item119

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

open scoped Matrix

private noncomputable def s16k_slEquivStatedSL (n : ℕ) (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin n) K ≃* ↥(StatedSL n K) :=
  (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL n K).symm)

private theorem s16k_slEquivStatedSL_apply_GL (n : ℕ) (K : Type) [Field K]
    (M : Matrix.SpecialLinearGroup (Fin n) K) :
    ((s16k_slEquivStatedSL n K M : ↥(StatedSL n K)) : GL (Fin n) K) =
      Matrix.SpecialLinearGroup.toGL M := by
  rw [s16k_slEquivStatedSL, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

private theorem s16k_slEquivStatedSL_symm_GL (n : ℕ) (K : Type) [Field K]
    (γ : ↥(StatedSL n K)) :
    Matrix.SpecialLinearGroup.toGL ((s16k_slEquivStatedSL n K).symm γ) = (γ : GL (Fin n) K) := by
  have h := s16k_slEquivStatedSL_apply_GL n K ((s16k_slEquivStatedSL n K).symm γ)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

private noncomputable def s16k_slMapEquiv {K L : Type} [Field K] [Field L] {n : ℕ}
    (e : K ≃+* L) : Matrix.SpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) L :=
  CFSG.RankThree.PartTwo.KFacts.slCongrOfRingEquiv n e

private theorem s16k_slMapEquiv_apply_coe {K L : Type} [Field K] [Field L] {n : ℕ}
    (e : K ≃+* L) (M : Matrix.SpecialLinearGroup (Fin n) K) :
    ((s16k_slMapEquiv e M : Matrix.SpecialLinearGroup (Fin n) L) :
        Matrix (Fin n) (Fin n) L) = e.mapMatrix (M : Matrix (Fin n) (Fin n) K) := rfl

private noncomputable def s16k_statedSLMap {K : Type} [Field K] {n : ℕ}
    (e : K ≃+* ZMod 2) :
    ↥(StatedSL n K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  (s16k_slEquivStatedSL n K).symm.trans (s16k_slMapEquiv e)

private theorem s16k_statedSLMap_apply_coe {K : Type} [Field K] {n : ℕ}
    (e : K ≃+* ZMod 2) (γ : ↥(StatedSL n K)) :
    ((s16k_statedSLMap e γ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
      e.mapMatrix ((γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hM : (((s16k_slEquivStatedSL n K).symm γ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K))
      (s16k_slEquivStatedSL_symm_GL n K γ)
  rw [s16k_statedSLMap, MulEquiv.trans_apply, s16k_slMapEquiv_apply_coe]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) K => e.mapMatrix M) hM

private noncomputable def s16k_vecEquiv {K L : Type*} [Field K] [Field L] {n : ℕ}
    (e : K ≃+* L) :
    Multiplicative (Fin n → K) ≃* Multiplicative (Fin n → L) where
  toFun x := Multiplicative.ofAdd (fun i => e (Multiplicative.toAdd x i))
  invFun x := Multiplicative.ofAdd (fun i => e.symm (Multiplicative.toAdd x i))
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [map_add]

private def s16k_vecMap {K L : Type*} {n : ℕ} (e : K → L) (v : Fin n → K) : Fin n → L :=
  fun i => e (v i)

private theorem s16k_toAdd_vecEquiv {K L : Type*} [Field K] [Field L] {n : ℕ}
    (e : K ≃+* L) (x : Multiplicative (Fin n → K)) :
    Multiplicative.toAdd (s16k_vecEquiv e x) = s16k_vecMap (⇑e) (Multiplicative.toAdd x) := rfl

private theorem s16k_vecMap_mulVec {K L : Type*} [Field K] [Field L] {n : ℕ}
    (e : K ≃+* L) (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    s16k_vecMap (⇑e) (M *ᵥ v) = (e.mapMatrix M) *ᵥ (s16k_vecMap (⇑e) v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, s16k_vecMap, Matrix.map_apply,
    RingEquiv.mapMatrix_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [map_mul]

private theorem s16k_vecMap_transpose_mulVec {K L : Type*} [Field K] [Field L] {n : ℕ}
    (e : K ≃+* L) (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    s16k_vecMap (⇑e) (Mᵀ *ᵥ v) = ((e.mapMatrix M)ᵀ) *ᵥ (s16k_vecMap (⇑e) v) := by
  rw [s16k_vecMap_mulVec]
  exact congrArg (fun N : Matrix (Fin n) (Fin n) L => N *ᵥ s16k_vecMap (⇑e) v)
    (Matrix.transpose_map (f := ⇑e) (M := M))

private noncomputable def s16k_mulVecEquiv {K : Type*} [Field K] {n : ℕ}
    (M : Matrix.SpecialLinearGroup (Fin n) K) :
    Multiplicative (Fin n → K) ≃* Multiplicative (Fin n → K) where
  toFun x := Multiplicative.ofAdd ((M : Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd x)
  invFun x :=
    Multiplicative.ofAdd
      ((M⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd x)
  left_inv x := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    rw [Matrix.mulVec_mulVec]
    simp
  right_inv x := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    rw [Matrix.mulVec_mulVec]
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul]
    rw [Matrix.mulVec_add]

private theorem s16k_mulVecEquiv_apply {K : Type*} [Field K] {n : ℕ}
    (M : Matrix.SpecialLinearGroup (Fin n) K) (x : Multiplicative (Fin n → K)) :
    Multiplicative.toAdd (s16k_mulVecEquiv M x) =
      (M : Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd x := rfl

private theorem s16k_vecEquiv_natAct {K : Type} [Field K] {n : ℕ} (e : K ≃+* ZMod 2)
    (γ : ↥(StatedSL n K)) (x : Multiplicative (Fin n → K)) :
    s16k_vecEquiv e (natAct (StatedSL n K) γ x) =
      s16k_mulVecEquiv (s16k_statedSLMap e γ) (s16k_vecEquiv e x) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [s16k_mulVecEquiv_apply, s16k_toAdd_vecEquiv]
  rw [show Multiplicative.toAdd (natAct (StatedSL n K) γ x) =
      (((γ : ↥(StatedSL n K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        Multiplicative.toAdd x from rfl]
  rw [s16k_vecMap_mulVec, ← s16k_statedSLMap_apply_coe, s16k_toAdd_vecEquiv]

private theorem s16k_vecEquiv_dualNatAct {K : Type} [Field K] {n : ℕ} (e : K ≃+* ZMod 2)
    (γ : ↥(StatedSL n K)) (x : Multiplicative (Fin n → K)) :
    s16k_vecEquiv e (dualNatAct (StatedSL n K) γ x) =
      s16k_mulVecEquiv
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2)
          (s16k_statedSLMap e γ)) (s16k_vecEquiv e x) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [s16k_mulVecEquiv_apply, s16k_toAdd_vecEquiv]
  rw [show Multiplicative.toAdd (dualNatAct (StatedSL n K) γ x) =
      ((((γ⁻¹ : ↥(StatedSL n K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ *ᵥ
        Multiplicative.toAdd x from rfl]
  rw [s16k_vecMap_transpose_mulVec, ← s16k_statedSLMap_apply_coe e (γ⁻¹), map_inv,
    ← CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix,
    s16k_toAdd_vecEquiv]

private noncomputable def s16k_vecConjEquiv {K₁ K₂ : Type} [Field K₁] [Field K₂] {n : ℕ}
    (e₁ : K₁ ≃+* ZMod 2) (e₂ : K₂ ≃+* ZMod 2)
    (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    Multiplicative (Fin n → K₁) ≃* Multiplicative (Fin n → K₂) :=
  (s16k_vecEquiv e₁).trans ((s16k_mulVecEquiv g).trans (s16k_vecEquiv e₂).symm)

private theorem s16k_vecEquiv_vecConjEquiv {K₁ K₂ : Type} [Field K₁] [Field K₂] {n : ℕ}
    (e₁ : K₁ ≃+* ZMod 2) (e₂ : K₂ ≃+* ZMod 2)
    (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (x : Multiplicative (Fin n → K₁)) :
    s16k_vecEquiv e₂ (s16k_vecConjEquiv e₁ e₂ g x) =
      s16k_mulVecEquiv g (s16k_vecEquiv e₁ x) := by
  simp [s16k_vecConjEquiv]

private theorem s16k_mulVec_conj_apply {K : Type*} [Field K] {n : ℕ}
    (g M : Matrix.SpecialLinearGroup (Fin n) K) (v : Fin n → K) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ ((M : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (((g * M * g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  have hmul : (Matrix.SpecialLinearGroup.toGL (g * M * g⁻¹) *
      Matrix.SpecialLinearGroup.toGL g : Matrix.GeneralLinearGroup (Fin n) K) =
      Matrix.SpecialLinearGroup.toGL g * Matrix.SpecialLinearGroup.toGL M := by
    rw [← map_mul]
    have hg : (g * M * g⁻¹) * g = g * M := by group
    rw [hg, map_mul]
  exact congrArg (fun u : Matrix.GeneralLinearGroup (Fin n) K =>
    (u : Matrix (Fin n) (Fin n) K)) hmul.symm

private theorem s16k_vecConjEquiv_natAct {K₁ K₂ : Type} [Field K₁] [Field K₂] {n : ℕ}
    (e₁ : K₁ ≃+* ZMod 2) (e₂ : K₂ ≃+* ZMod 2)
    (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (γ₁ : ↥(StatedSL n K₁)) (γ₂ : ↥(StatedSL n K₂))
    (x : Multiplicative (Fin n → K₁))
    (h : s16k_statedSLMap e₂ γ₂ = g * s16k_statedSLMap e₁ γ₁ * g⁻¹) :
    s16k_vecConjEquiv e₁ e₂ g (natAct (StatedSL n K₁) γ₁ x) =
      natAct (StatedSL n K₂) γ₂ (s16k_vecConjEquiv e₁ e₂ g x) := by
  apply (s16k_vecEquiv e₂).injective
  rw [s16k_vecEquiv_natAct e₂ γ₂ (s16k_vecConjEquiv e₁ e₂ g x),
    s16k_vecEquiv_vecConjEquiv, s16k_vecEquiv_vecConjEquiv, s16k_vecEquiv_natAct e₁ γ₁ x, h]
  apply Multiplicative.toAdd.injective
  simp only [s16k_mulVecEquiv_apply]
  exact s16k_mulVec_conj_apply g (s16k_statedSLMap e₁ γ₁)
    (Multiplicative.toAdd (s16k_vecEquiv e₁ x))

private theorem s16k_vecConjEquiv_dualNatAct {K₁ K₂ : Type} [Field K₁] [Field K₂] {n : ℕ}
    (e₁ : K₁ ≃+* ZMod 2) (e₂ : K₂ ≃+* ZMod 2)
    (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (γ₁ : ↥(StatedSL n K₁)) (γ₂ : ↥(StatedSL n K₂))
    (x : Multiplicative (Fin n → K₁))
    (h : s16k_statedSLMap e₂ γ₂ =
      g * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2)
        (s16k_statedSLMap e₁ γ₁) * g⁻¹) :
    s16k_vecConjEquiv e₁ e₂ g (dualNatAct (StatedSL n K₁) γ₁ x) =
      natAct (StatedSL n K₂) γ₂ (s16k_vecConjEquiv e₁ e₂ g x) := by
  apply (s16k_vecEquiv e₂).injective
  rw [s16k_vecEquiv_natAct e₂ γ₂ (s16k_vecConjEquiv e₁ e₂ g x),
    s16k_vecEquiv_vecConjEquiv, s16k_vecEquiv_vecConjEquiv,
    s16k_vecEquiv_dualNatAct e₁ γ₁ x, h]
  apply Multiplicative.toAdd.injective
  simp only [s16k_mulVecEquiv_apply]
  exact s16k_mulVec_conj_apply g
    (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2)
      (s16k_statedSLMap e₁ γ₁)) (Multiplicative.toAdd (s16k_vecEquiv e₁ x))

theorem s16k_sl_two_equiv {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X] [Finite X]
    (hX : IsSLn X n 1) {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
    (h₁ : Nat.card K₁ = 2) (h₂ : Nat.card K₂ = 2) {π₁ : ↥(StatedSL n K₁) →* X}
    {π₂ : ↥(StatedSL n K₂) →* X} (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂) :
    Function.Injective π₁ ∧ Function.Injective π₂ ∧
      (S16kModelsEquivVia (FFModel.nat (StatedSL n K₁)) (FFModel.nat (StatedSL n K₁)).act
          (FFModel.nat (StatedSL n K₂)) π₁ π₂ ∨
        S16kModelsEquivVia (FFModel.nat (StatedSL n K₁)) (dualNatAct (StatedSL n K₁))
          (FFModel.nat (StatedSL n K₂)) π₁ π₂) := by
  classical
  obtain ⟨K', hK'field, hK'fin, hK'card, ⟨eX⟩⟩ := hX
  haveI : Fintype K₁ := Fintype.ofFinite K₁
  haveI : Fintype K₂ := Fintype.ofFinite K₂
  haveI : Fintype K' := Fintype.ofFinite K'
  have hK' : Nat.card K' = 2 := by simpa using hK'card
  let e₁ : K₁ ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h₁, Nat.card_zmod])
  let e₂ : K₂ ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h₂, Nat.card_zmod])
  let e' : K' ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK', Nat.card_zmod])
  have hcard₁ : Nat.card ↥(StatedSL n K₁) =
      Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr (s16k_statedSLMap e₁).toEquiv
  have hcard₂ : Nat.card ↥(StatedSL n K₂) =
      Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr (s16k_statedSLMap e₂).toEquiv
  have hcardX : Nat.card X = Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    have h1 : Nat.card X = Nat.card ↥(StatedSL n K') := Nat.card_congr eX.toEquiv
    rw [h1, Nat.card_congr (s16k_statedSLMap e').toEquiv]
  have hbij₁ : Function.Bijective π₁ := hπ₁.bijective_of_nat_card_le (by rw [hcard₁, hcardX])
  have hbij₂ : Function.Bijective π₂ := hπ₂.bijective_of_nat_card_le (by rw [hcard₂, hcardX])
  have hinj₁ : Function.Injective π₁ := hbij₁.1
  have hinj₂ : Function.Injective π₂ := hbij₂.1
  let φ : ↥(StatedSL n K₁) ≃* ↥(StatedSL n K₂) :=
    (MulEquiv.ofBijective π₁ hbij₁).trans (MulEquiv.ofBijective π₂ hbij₂).symm
  have hφ_apply : ∀ γ : ↥(StatedSL n K₁), π₂ (φ γ) = π₁ γ := by
    intro γ
    dsimp only [φ]
    rw [MulEquiv.trans_apply]
    rw [show π₂ ((MulEquiv.ofBijective π₂ hbij₂).symm ((MulEquiv.ofBijective π₁ hbij₁) γ)) =
        (MulEquiv.ofBijective π₂ hbij₂) ((MulEquiv.ofBijective π₂ hbij₂).symm
          ((MulEquiv.ofBijective π₁ hbij₁) γ)) from rfl]
    rw [MulEquiv.apply_symm_apply, MulEquiv.ofBijective_apply]
  let β : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    (s16k_statedSLMap e₁).symm.trans (φ.trans (s16k_statedSLMap e₂))
  have hβφ : ∀ (γ₁ : ↥(StatedSL n K₁)) (γ₂ : ↥(StatedSL n K₂)),
      π₁ γ₁ = π₂ γ₂ → s16k_statedSLMap e₂ γ₂ = β (s16k_statedSLMap e₁ γ₁) := by
    intro γ₁ γ₂ hπ
    have hγ : φ γ₁ = γ₂ := by
      apply hinj₂
      rw [hφ_apply γ₁, hπ]
    have : β (s16k_statedSLMap e₁ γ₁) = s16k_statedSLMap e₂ γ₂ := by
      dsimp only [β]
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hγ]
    exact this.symm
  obtain ⟨g, ε, hε, hβ⟩ := CFSG.RankThree.PartOne.TAIL.aut_sl_zmod_two hn β
  let A : (FFModel.nat (StatedSL n K₁)).Amb ≃* (FFModel.nat (StatedSL n K₂)).Amb :=
    s16k_vecConjEquiv e₁ e₂ g
  refine ⟨hinj₁, hinj₂, ?_⟩
  interval_cases ε
  · left
    refine ⟨A, ?_, ?_, ?_⟩
    · intro m
      exact iff_of_true (Subgroup.mem_top m) (Subgroup.mem_top (A m))
    · intro m
      have hk₁ : (FFModel.nat (StatedSL n K₁)).ker = ⊥ := rfl
      have hk₂ : (FFModel.nat (StatedSL n K₂)).ker = ⊥ := rfl
      rw [hk₁, hk₂, Subgroup.mem_bot, Subgroup.mem_bot]
      exact A.map_eq_one_iff.symm
    · intro γ₁ γ₂ hπ m
      exact s16k_vecConjEquiv_natAct e₁ e₂ g γ₁ γ₂ m (by
        rw [hβφ γ₁ γ₂ hπ, hβ]
        simp [MulAut.conj_apply])
  · right
    refine ⟨A, ?_, ?_, ?_⟩
    · intro m
      exact iff_of_true (Subgroup.mem_top m) (Subgroup.mem_top (A m))
    · intro m
      have hk₁ : (FFModel.nat (StatedSL n K₁)).ker = ⊥ := rfl
      have hk₂ : (FFModel.nat (StatedSL n K₂)).ker = ⊥ := rfl
      rw [hk₁, hk₂, Subgroup.mem_bot, Subgroup.mem_bot]
      exact A.map_eq_one_iff.symm
    · intro γ₁ γ₂ hπ m
      exact s16k_vecConjEquiv_dualNatAct e₁ e₂ g γ₁ γ₂ m (by
        rw [hβφ γ₁ γ₂ hπ, hβ]
        simp [MulAut.conj_apply])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo