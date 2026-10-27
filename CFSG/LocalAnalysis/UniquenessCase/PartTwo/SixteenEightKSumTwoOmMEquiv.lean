module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoDef
public import CFSG.Open.StatedZModTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleGraph
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open CFSG.ClassicalInvolution.Upgrade (map_statedOmega statedQuadMinus_comp)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open scoped Matrix

private theorem s16k_field_two {K : Type} [Field K] [Finite K] (hcard : Nat.card K = 2) :
    Nonempty (K ≃+* ZMod 2) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  exact ⟨(ZMod.ringEquivOfPrime K Nat.prime_two hK').symm⟩

private theorem s16k_bc_eq_one {K : Type} [Field K] (e : K ≃+* ZMod 2) {b c : K}
    (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : e b = 1 ∧ e c = 1 := by
  have hpoly' : ∀ t : ZMod 2, t ^ 2 + e b * t + e c ≠ 0 := by
    intro t h0
    apply hpoly (e.symm t)
    apply e.injective
    simpa using h0
  have h0 := hpoly' 0
  have h1 := hpoly' 1
  generalize e b = x at h0 h1 ⊢
  generalize e c = y at h0 h1 ⊢
  revert x y
  decide

private theorem s16k_minus_bc_eq_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b = 1 ∧ c = 1 := by
  obtain ⟨e⟩ := s16k_field_two hK
  obtain ⟨hb, hc⟩ := s16k_bc_eq_one e hirr
  refine ⟨?_, ?_⟩
  · rw [← e.symm_apply_apply b, hb]
    exact map_one e.symm
  · rw [← e.symm_apply_apply c, hc]
    exact map_one e.symm

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

private theorem s16k_natAct_toAdd {K : Type} [Field K] {m : ℕ} {b c : K}
    (g : ↥(StatedOmega (StatedQuadMinus m K b c)))
    (x : Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) :
    (natAct (StatedOmega (StatedQuadMinus m K b c)) g x).toAdd =
      (((g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ x.toAdd := rfl

private noncomputable def s16k_statedOmegaMinusCongr {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) {m : ℕ} {b c : K} {b' c' : L} (hb : e b = b') (hc : e c = c') :
    ↥(StatedOmega (StatedQuadMinus m K b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus m L b' c')) :=
  ((glCongr (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) e).subgroupMap
    (StatedOmega (StatedQuadMinus m K b c))).trans
    (MulEquiv.subgroupCongr (map_statedOmega e (statedQuadMinus_comp e hb hc)))

private theorem s16k_statedOmegaMinusCongr_apply_coe {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) {m : ℕ} {b c : K} {b' c' : L} (hb : e b = b') (hc : e c = c')
    (x : ↥(StatedOmega (StatedQuadMinus m K b c))) :
    ((s16k_statedOmegaMinusCongr e hb hc x :
        ↥(StatedOmega (StatedQuadMinus m L b' c'))) :
        GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) L) =
      glCongr e (x : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) := by
  simp only [s16k_statedOmegaMinusCongr, MulEquiv.trans_apply, MulEquiv.coe_subgroupMap_apply,
    MulEquiv.subgroupCongr_apply]
  rfl

private noncomputable def s16k_statedOmegaMinusProjEquiv {K : Type} [Field K]
    (hK : Nat.card K = 2) {m : ℕ} {b c : K} :
    ↥(StatedOmega (StatedQuadMinus m K b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus m K b c)) :=
  let hsub : (StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus m K b c)) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK, Subgroup.bot_subgroupOf]
  (QuotientGroup.quotientBot (G := ↥(StatedOmega (StatedQuadMinus m K b c)))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hsub.symm)

private theorem s16k_statedOmegaMinusProjEquiv_apply_mk {K : Type} [Field K]
    (hK : Nat.card K = 2) {m : ℕ} {b c : K}
    (x : ↥(StatedOmega (StatedQuadMinus m K b c))) :
    s16k_statedOmegaMinusProjEquiv hK x = QuotientGroup.mk x := by
  simp [s16k_statedOmegaMinusProjEquiv]

theorem s16k_omegaMinus_module_equiv {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
    (h₁ : Nat.card K₁ = 2) (h₂ : Nat.card K₂ = 2) {m : ℕ} (hm : 5 ≤ m) {b₁ c₁ : K₁} {b₂ c₂ : K₂}
    (hirr₁ : ∀ s : K₁, s ^ 2 + b₁ * s + c₁ ≠ 0) (hirr₂ : ∀ s : K₂, s ^ 2 + b₂ * s + c₂ ≠ 0)
    (φ : ↥(StatedOmega (StatedQuadMinus m K₁ b₁ c₁)) ≃*
      ↥(StatedOmega (StatedQuadMinus m K₂ b₂ c₂))) :
    ∃ A : Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K₁) ≃*
        Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K₂),
      ∀ (γ : ↥(StatedOmega (StatedQuadMinus m K₁ b₁ c₁)))
        (x : Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K₁)),
        A (natAct (StatedOmega (StatedQuadMinus m K₁ b₁ c₁)) γ x) =
          natAct (StatedOmega (StatedQuadMinus m K₂ b₂ c₂)) (φ γ) (A x) := by
  haveI : Fintype K₁ := Fintype.ofFinite K₁
  haveI : Fintype K₂ := Fintype.ofFinite K₂
  let e : K₁ ≃+* K₂ := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, h₁, h₂])
  obtain ⟨hb₁, hc₁⟩ := s16k_minus_bc_eq_one h₁ hirr₁
  obtain ⟨hb₂, hc₂⟩ := s16k_minus_bc_eq_one h₂ hirr₂
  have hb : e b₁ = b₂ := by rw [hb₁, hb₂, map_one]
  have hc : e c₁ = c₂ := by rw [hc₁, hc₂, map_one]
  let E : ↥(StatedOmega (StatedQuadMinus m K₁ b₁ c₁)) ≃*
      ↥(StatedOmega (StatedQuadMinus m K₂ b₂ c₂)) :=
    s16k_statedOmegaMinusCongr e hb hc
  let ψ : ↥(StatedOmega (StatedQuadMinus m K₁ b₁ c₁)) ≃*
      ↥(StatedOmega (StatedQuadMinus m K₁ b₁ c₁)) :=
    φ.trans E.symm
  let j : ↥(StatedOmega (StatedQuadMinus m K₁ b₁ c₁)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus m K₁ b₁ c₁)) :=
    s16k_statedOmegaMinusProjEquiv h₁
  let β : MulAut (StatedProj (StatedOmega (StatedQuadMinus m K₁ b₁ c₁))) :=
    { toFun := fun q => j (ψ (j.symm q))
      invFun := fun q => j (ψ.symm (j.symm q))
      left_inv := fun q => by simp
      right_inv := fun q => by simp
      map_mul' := fun q r => by simp [map_mul] }
  have hβj : ∀ x, β (j x) = j (ψ x) := by intro x; simp [β]
  obtain ⟨σ, A, μ, hμ, hAQ, hβ⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.exists_semilinear_minus (n := m) (by omega)
      hirr₁ β
  have hσ : σ = (1 : K₁ ≃+* K₁) :=
    CFSG.ComponentClassification.OutcomeLocal.ringEquiv_eq_one_of_card_two h₁ σ
  have hglAut : ∀ g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁, glAut σ g = g := by
    intro g
    rw [hσ]
    exact congrArg (fun (φ : MulAut (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁)) => φ g)
      (map_one glAut)
  have hψg : ∀ g : ↥(StatedOmega (StatedQuadMinus m K₁ b₁ c₁)),
      ∃ hg : A * glAut σ (g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁) * A⁻¹ ∈
        StatedOmega (StatedQuadMinus m K₁ b₁ c₁),
        ψ g = ⟨A * glAut σ (g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁) * A⁻¹, hg⟩ := by
    intro g
    obtain ⟨hg, hβg⟩ := hβ g
    refine ⟨hg, ?_⟩
    apply j.injective
    rw [← hβj g, s16k_statedOmegaMinusProjEquiv_apply_mk h₁ g, hβg,
      s16k_statedOmegaMinusProjEquiv_apply_mk h₁ ⟨_, hg⟩]
  have hφg : ∀ g : ↥(StatedOmega (StatedQuadMinus m K₁ b₁ c₁)),
      (φ g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) =
        glCongr e (A * (g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁) * A⁻¹) := by
    intro g
    obtain ⟨hg, hψg'⟩ := hψg g
    have hE : E (ψ g) = φ g := by
      show E ((φ.trans E.symm) g) = φ g
      rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h1 : E (⟨A * glAut σ (g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁) * A⁻¹, hg⟩) =
        φ g := by
      rw [← hψg']
      exact hE
    have h2 : glCongr e (A * glAut σ (g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁) * A⁻¹) =
        (φ g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) := by
      have h3 := congrArg (fun z : ↥(StatedOmega (StatedQuadMinus m K₂ b₂ c₂)) =>
        (z : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂)) h1
      rwa [s16k_statedOmegaMinusCongr_apply_coe] at h3
    rw [← h2, hglAut]
  have hmat : ∀ g : ↥(StatedOmega (StatedQuadMinus m K₁ b₁ c₁)),
      (((φ g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂)) :
          Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) *
          (A : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁).map e =
        (A : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁).map e *
          (((g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁)) :
            Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
              (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁).map e := by
    intro g
    have hGL : (φ g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂) * glCongr e A =
        glCongr e A * glCongr e (g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₁) := by
      rw [hφg g, ← map_mul, ← map_mul]
      congr 1
      group
    have h4 := congrArg (fun u : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂ =>
      (u : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
        (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K₂)) hGL
    simpa [glCongr_coe, Units.val_mul] using h4
  refine ⟨s16k_vecConjMulEquiv e A, ?_⟩
  intro g x
  apply Multiplicative.toAdd.injective
  rw [s16k_vecConjMulEquiv_apply_toAdd, s16k_natAct_toAdd, s16k_vecMap_mulVec,
    Matrix.mulVec_mulVec]
  conv_rhs => rw [s16k_natAct_toAdd, s16k_vecConjMulEquiv_apply_toAdd, Matrix.mulVec_mulVec]
  rw [hmat g]

private theorem s16k_omegaMinus_injective {m : ℕ} (hm : 4 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {X : Type} [Group X] [Nontrivial X]
    (π : ↥(StatedOmega (StatedQuadMinus m K b c)) →* X) (hπ : Function.Surjective π) :
    Function.Injective π := by
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus m K b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus (K := K)
      (n := m) (b := b) (c := c) hm hirr
  let G := ↥(StatedOmega (StatedQuadMinus m K b c))
  have hscal : StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK _
  have hsub : (StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus m K b c)) = ⊥ := by
    rw [hscal, Subgroup.bot_subgroupOf]
  haveI : IsSimpleGroup G := by
    let e : G ≃* StatedProj (StatedOmega (StatedQuadMinus m K b c)) :=
      ((QuotientGroup.quotientMulEquivOfEq hsub).trans QuotientGroup.quotientBot).symm
    exact MulEquiv.isSimpleGroup e
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.ker π) with h | h
  · exact h
  · exfalso
    have hrange : MonoidHom.range π = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro y ⟨g, rfl⟩
      exact MonoidHom.mem_ker.mp (by rw [h]; exact Subgroup.mem_top g)
    have hbot : (⊥ : Subgroup X) = ⊤ := by
      rw [← hrange, MonoidHom.range_eq_top.mpr hπ]
    have hsingle : Subsingleton X := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup X) := by rw [hbot]; exact Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup X) := by rw [hbot]; exact Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    exact not_subsingleton X hsingle

theorem s16k_omegaMinus_two_equiv {n : ℕ} (hn : 10 ≤ n) {X : Type} [Group X] [Finite X]
    (hX : IsOmegaMinus X n 1) {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
    (h₁ : Nat.card K₁ = 2) (h₂ : Nat.card K₂ = 2) {b₁ c₁ : K₁} {b₂ c₂ : K₂}
    (hirr₁ : ∀ s : K₁, s ^ 2 + b₁ * s + c₁ ≠ 0) (hirr₂ : ∀ s : K₂, s ^ 2 + b₂ * s + c₂ ≠ 0)
    {π₁ : ↥(StatedOmega (StatedQuadMinus (n / 2) K₁ b₁ c₁)) →* X}
    {π₂ : ↥(StatedOmega (StatedQuadMinus (n / 2) K₂ b₂ c₂)) →* X}
    (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂) :
    Function.Injective π₁ ∧ Function.Injective π₂ ∧
      S16kModelsEquivVia (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K₁ b₁ c₁)))
        (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K₁ b₁ c₁))).act
        (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K₂ b₂ c₂))) π₁ π₂ := by
  classical
  obtain ⟨-, K', hK'f, hK'fin, b', c', -, hirr', hX⟩ := hX
  obtain ⟨eX⟩ := hX
  letI : Field K' := hK'f
  letI : Finite K' := hK'fin
  have hm : 4 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hm5 : 5 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K' b' c'))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus (K := K')
      (n := n / 2) (b := b') (c := c') (by omega) hirr'
  haveI : IsSimpleGroup X := MulEquiv.isSimpleGroup eX
  have hinj₁ : Function.Injective π₁ := s16k_omegaMinus_injective hm h₁ hirr₁ π₁ hπ₁
  have hinj₂ : Function.Injective π₂ := s16k_omegaMinus_injective hm h₂ hirr₂ π₂ hπ₂
  let π₁e : ↥(StatedOmega (StatedQuadMinus (n / 2) K₁ b₁ c₁)) ≃* X :=
    MulEquiv.ofBijective π₁ ⟨hinj₁, hπ₁⟩
  let π₂e : ↥(StatedOmega (StatedQuadMinus (n / 2) K₂ b₂ c₂)) ≃* X :=
    MulEquiv.ofBijective π₂ ⟨hinj₂, hπ₂⟩
  let φ : ↥(StatedOmega (StatedQuadMinus (n / 2) K₁ b₁ c₁)) ≃*
      ↥(StatedOmega (StatedQuadMinus (n / 2) K₂ b₂ c₂)) := π₁e.trans π₂e.symm
  obtain ⟨A, hA⟩ := s16k_omegaMinus_module_equiv h₁ h₂ hm5 hirr₁ hirr₂ φ
  refine ⟨hinj₁, hinj₂, A, ?_, ?_, ?_⟩
  · intro x
    exact iff_of_true (Subgroup.mem_top x) (Subgroup.mem_top (A x))
  · intro x
    have hk₁ : (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K₁ b₁ c₁))).ker = ⊥ := rfl
    have hk₂ : (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K₂ b₂ c₂))).ker = ⊥ := rfl
    rw [hk₁, hk₂, Subgroup.mem_bot, Subgroup.mem_bot]
    exact (MulEquiv.map_eq_one_iff A).symm
  · intro γ₁ γ₂ hγ x
    have h1 : π₁e γ₁ = π₂e γ₂ := by
      change π₁ γ₁ = π₂ γ₂
      exact hγ
    have hφ : φ γ₁ = γ₂ := by
      change π₂e.symm (π₁e γ₁) = γ₂
      rw [h1]
      exact MulEquiv.symm_apply_apply π₂e γ₂
    change A (natAct (StatedOmega (StatedQuadMinus (n / 2) K₁ b₁ c₁)) γ₁ x) =
      natAct (StatedOmega (StatedQuadMinus (n / 2) K₂ b₂ c₂)) γ₂ (A x)
    rw [← hφ]
    exact hA γ₁ x

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
