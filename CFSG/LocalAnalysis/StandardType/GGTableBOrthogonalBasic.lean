module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticCover
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEight
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
public import CFSG.RankThree.PartOne.AUTSL.Rows
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBOrth

variable {K : Type} [Field K]

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isometry_of_mem_orthGroup {Q : (ι → K) → K} {g : GL ι K}
    (hg : g ∈ LargeEvenOrthGroup Q) (v : ι → K) : Q ((g : Matrix ι ι K) *ᵥ v) = Q v := by
  induction hg using Subgroup.closure_induction generalizing v with
  | mem g hg => exact hg v
  | one => simp
  | mul g h _ _ hg hh => rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg, hh]
  | inv g _ hg =>
    have h1 := hg (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h1
    exact h1.symm

theorem omega_le_orth (Q : (ι → K) → K) : LargeEvenOmega Q ≤ LargeEvenOrthGroup Q :=
  Subgroup.commutator_le_self _

theorem eq_zero_of_commute_diagonal {g : Matrix ι ι K} {δ : ι → K}
    (h : g * Matrix.diagonal δ = Matrix.diagonal δ * g) {i j : ι} (hij : δ i ≠ δ j) :
    g i j = 0 := by
  have e := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  have e' : (δ i - δ j) * g i j = 0 := by linear_combination -e
  exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr hij)

theorem commute_diagGL_iff {g : GL ι K} {δ : ι → Kˣ} :
    g * TauCeti.diagGL δ = TauCeti.diagGL δ * g ↔
      (g : Matrix ι ι K) * Matrix.diagonal (fun i => (δ i : K)) =
        Matrix.diagonal (fun i => (δ i : K)) * (g : Matrix ι ι K) := by
  rw [← TauCeti.diagGL_coe, ← Units.val_mul, ← Units.val_mul, Units.ext_iff]

theorem eq_one_of_scalar_isometry [CharP K 2] {Q : (ι → K) → K}
    (hQs : ∀ (c : K) (v : ι → K), Q (c • v) = c ^ 2 * Q v) {v₀ : ι → K} (hv₀ : Q v₀ ≠ 0)
    {c : Kˣ} (h : ∀ v, Q ((Matrix.GeneralLinearGroup.scalar ι c : Matrix ι ι K) *ᵥ v) = Q v) :
    c = 1 := by
  have h1 := h v₀
  have h2 : (Matrix.GeneralLinearGroup.scalar ι c : Matrix ι ι K) *ᵥ v₀ = (c : K) • v₀ := by
    funext i
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rfl
  rw [h2, hQs] at h1
  have h3 : ((c : K) - 1) ^ 2 * Q v₀ = 0 := by
    have : ((c : K) - 1) ^ 2 = (c : K) ^ 2 - 1 := by
      linear_combination (1 - (c : K)) * (CharTwo.two_eq_zero (R := K))
    rw [this]
    linear_combination h1
  have h4 : ((c : K) - 1) ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_right hv₀
  apply Units.ext
  rw [Units.val_one]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h4)

theorem scalars_subgroupOf_omega_eq_bot [CharP K 2] {Q : (ι → K) → K}
    (hQs : ∀ (c : K) (v : ι → K), Q (c • v) = c ^ 2 * Q v) {v₀ : ι → K} (hv₀ : Q v₀ ≠ 0) :
    (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hgΩ⟩ hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  change Matrix.GeneralLinearGroup.scalar ι c = g at hc
  have hiso := isometry_of_mem_orthGroup (omega_le_orth Q hgΩ)
  have hc1 : c = 1 := eq_one_of_scalar_isometry hQs hv₀ (by
    intro v
    have := hiso v
    rwa [← hc] at this)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  change g = 1
  rw [← hc, hc1, map_one]

@[expose] noncomputable def projMkEquiv {Q : (ι → K) → K}
    (h : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥) :
    LargeEvenOmega Q ≃* LargeEvenProj (LargeEvenOmega Q) :=
  MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenOmega Q))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro x hx
      have : x ∈ (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) :=
        (QuotientGroup.eq_one_iff x).mp hx
      rw [h, Subgroup.mem_bot] at this
      exact this,
     QuotientGroup.mk'_surjective _⟩

theorem projMkEquiv_apply {Q : (ι → K) → K}
    (h : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥) (x : LargeEvenOmega Q) :
    projMkEquiv h x = (x : LargeEvenProj (LargeEvenOmega Q)) :=
  rfl

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G] {x y : G}
    (hxy : x * y ≠ y * x) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    apply hxy
    have hx : x ∈ Subgroup.center G := h ▸ Subgroup.mem_top x
    exact (Subgroup.mem_center_iff.mp hx y).symm

end General

section Singular

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem two_mul_finrank_le_of_singular {Q : QuadraticForm K V}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) {T : Submodule K V}
    (hT : ∀ w ∈ T, Q w = 0) : 2 * Module.finrank K T ≤ Module.finrank K V := by
  have hle : T ≤ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) T := by
    intro y hy
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    change QuadraticMap.polar Q x y = 0
    rw [QuadraticMap.polar, hT _ (T.add_mem hx hy), hT x hx, hT y hy, sub_zero, sub_zero]
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hnd] at h1
  have h2 := Submodule.finrank_le T
  omega

omit [FiniteDimensional K V] in
theorem finrank_le_of_isometryEquiv {V' : Type*} [AddCommGroup V'] [Module K V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (e : Q.IsometryEquiv Q') {r : ℕ}
    (h : ∀ T : Submodule K V', (∀ w ∈ T, Q' w = 0) → Module.finrank K T ≤ r)
    (T : Submodule K V) (hT : ∀ w ∈ T, Q w = 0) : Module.finrank K T ≤ r := by
  have hmap : ∀ w ∈ T.map e.toLinearEquiv.toLinearMap, Q' w = 0 := by
    rintro _ ⟨w, hw, rfl⟩
    change Q' (e w) = 0
    rw [e.map_app, hT w hw]
  have := h _ hmap
  rwa [LinearEquiv.finrank_map_eq] at this

end Singular

section Plus

open CFSG.LieType.Universal.Spin

variable (K) in
@[expose] noncomputable def qPlusForm (m : ℕ) : QuadraticForm K (Fin m ⊕ Fin m → K) :=
  quadPlus m K

theorem coe_qPlusForm (m : ℕ) : ⇑(qPlusForm K m) = LargeEvenQPlus K m :=
  coe_quadPlus m K

theorem nondegenerate_qPlusForm (m : ℕ) :
    (QuadraticMap.polarBilin (qPlusForm K m)).Nondegenerate :=
  nondegenerate_polarBilin_quadPlus m K

theorem isHypCoord_qPlusForm {m : ℕ} (k : Fin m) :
    SeitzReduction.OmegaPilot.IsHypCoord (qPlusForm K m) (Sum.inl k) (Sum.inr k) where
  ne := Sum.inl_ne_inr
  map_left := by
    rw [qPlusForm, quadPlus_apply]
    simp [Pi.single_apply]
  map_right := by
    rw [qPlusForm, quadPlus_apply]
    simp [Pi.single_apply]
  polar_left v := by
    rw [QuadraticMap.polar_comm, qPlusForm, polar_quadPlus_single_inl]
  polar_right v := by
    rw [QuadraticMap.polar_comm, qPlusForm, polar_quadPlus_single_inr]

theorem finrank_le_of_singular_qPlus {m : ℕ} (T : Submodule K (Fin m ⊕ Fin m → K))
    (hT : ∀ w ∈ T, qPlusForm K m w = 0) : Module.finrank K T ≤ m := by
  have h := two_mul_finrank_le_of_singular (nondegenerate_qPlusForm m) hT
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h
  omega

theorem largeEvenQPlus_smul (m : ℕ) (c : K) (v : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m (c • v) = c ^ 2 * LargeEvenQPlus K m v := by
  rw [← coe_qPlusForm, QuadraticMap.map_smul, smul_eq_mul, sq]

theorem largeEvenQPlus_single_add_single {m : ℕ} (k : Fin m) :
    LargeEvenQPlus K m (Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr k) 1) = 1 := by
  rw [← coe_qPlusForm]
  have := (isHypCoord_qPlusForm (K := K) k).map_single_add
  exact this

end Plus

theorem polar_comp_linearMap {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (Q : QuadraticForm K V') (f : V →ₗ[K] V') (x y : V) :
    QuadraticMap.polar (Q.comp f) x y = QuadraticMap.polar Q (f x) (f y) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]

section Minus

open CFSG.LieType.Universal.Spin

variable (K) in
@[expose] noncomputable def minusAssoc (m : ℕ) :
    (LargeEvenMinusIdx m → K) ≃ₗ[K] (Fin m ⊕ (Fin m ⊕ Fin 2) → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.sumAssoc (Fin m) (Fin m) (Fin 2)).symm

theorem minusAssoc_apply (m : ℕ) (w : LargeEvenMinusIdx m → K) (x : Fin m ⊕ (Fin m ⊕ Fin 2)) :
    minusAssoc K m w x = w ((Equiv.sumAssoc (Fin m) (Fin m) (Fin 2)).symm x) :=
  rfl

variable (K) in
@[expose] noncomputable def qMinusForm (m : ℕ) (b c : K) :
    QuadraticForm K (LargeEvenMinusIdx m → K) :=
  (quadMinus (m + 1) K b c).comp (minusAssoc K m).toLinearMap

theorem coe_qMinusForm (m : ℕ) (b c : K) : ⇑(qMinusForm K m b c) = LargeEvenQMinus m b c := by
  funext w
  rw [qMinusForm, QuadraticMap.comp_apply, quadMinus_apply]
  simp only [LinearEquiv.coe_coe, minusAssoc_apply, LargeEvenQMinus]
  rfl

@[expose] noncomputable def qMinusIsometry (m : ℕ) (b c : K) :
    (qMinusForm K m b c).IsometryEquiv (quadMinus (m + 1) K b c) where
  toLinearEquiv := minusAssoc K m
  map_app' _ := rfl

theorem nondegenerate_qMinusForm [Finite K] (m : ℕ) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (QuadraticMap.polarBilin (qMinusForm K m b c)).Nondegenerate :=
  CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.polar_nondegenerate_isometry
    (qMinusIsometry m b c).symm (nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hirr)

theorem minusAssoc_single_inl_inl (m : ℕ) (k : Fin m) :
    minusAssoc K m (Pi.single (Sum.inl (Sum.inl k)) 1) = Pi.single (Sum.inl k) 1 := by
  funext x
  rw [minusAssoc_apply]
  rcases x with x | x | x <;> simp [Pi.single_apply]

theorem minusAssoc_single_inl_inr (m : ℕ) (k : Fin m) :
    minusAssoc K m (Pi.single (Sum.inl (Sum.inr k)) 1) = Pi.single (Sum.inr (Sum.inl k)) 1 := by
  funext x
  rw [minusAssoc_apply]
  rcases x with x | x | x <;> simp [Pi.single_apply]

theorem isHypCoord_qMinusForm {m : ℕ} (b c : K) (k : Fin m) :
    SeitzReduction.OmegaPilot.IsHypCoord (qMinusForm K m b c) (Sum.inl (Sum.inl k))
      (Sum.inl (Sum.inr k)) where
  ne := fun h => Sum.inl_ne_inr (Sum.inl_injective h)
  map_left := by
    rw [qMinusForm, QuadraticMap.comp_apply, LinearEquiv.coe_coe, minusAssoc_single_inl_inl,
      quadMinus_apply]
    simp [Pi.single_apply]
  map_right := by
    rw [qMinusForm, QuadraticMap.comp_apply, LinearEquiv.coe_coe, minusAssoc_single_inl_inr,
      quadMinus_apply]
    simp [Pi.single_apply]
  polar_left v := by
    rw [qMinusForm, polar_comp_linearMap, LinearEquiv.coe_coe, minusAssoc_single_inl_inl,
      QuadraticMap.polar_comm, polar_quadMinus_single_inl, minusAssoc_apply]
    rfl
  polar_right v := by
    rw [qMinusForm, polar_comp_linearMap, LinearEquiv.coe_coe, minusAssoc_single_inl_inr,
      QuadraticMap.polar_comm, polar_quadMinus_single_inr_inl, minusAssoc_apply]
    rfl

theorem finrank_le_of_singular_qMinus [Finite K] {m : ℕ} {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (T : Submodule K (LargeEvenMinusIdx m → K))
    (hT : ∀ w ∈ T, qMinusForm K m b c w = 0) : Module.finrank K T ≤ m := by
  have e := (qMinusIsometry (K := K) m b c).trans
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusIsometry (m + 1) K
      (by omega) b c)
  have h := (SeitzReduction.OmegaPilot.regular_wittIndex_coordinateQuadMinus (K := K)
    (m := m + 1) (by omega) hirr).2
  exact finrank_le_of_isometryEquiv e (fun T hT => (h T hT).trans (by omega)) T hT

theorem largeEvenQMinus_smul (m : ℕ) (b c x : K) (v : LargeEvenMinusIdx m → K) :
    LargeEvenQMinus m b c (x • v) = x ^ 2 * LargeEvenQMinus m b c v := by
  rw [← coe_qMinusForm, QuadraticMap.map_smul, smul_eq_mul, sq]

theorem largeEvenQMinus_single_add_single {m : ℕ} (b c : K) (k : Fin m) :
    LargeEvenQMinus m b c (Pi.single (Sum.inl (Sum.inl k)) 1 +
      Pi.single (Sum.inl (Sum.inr k)) 1) = 1 := by
  rw [← coe_qMinusForm]
  exact (isHypCoord_qMinusForm (K := K) b c k).map_single_add

end Minus

section Center

open TableBSymp

theorem siegelGL_injective {m : ℕ} {i₀ i₁ : Fin m} (h01 : i₁ ≠ i₀) {c c' : K}
    (h : siegelGL i₀ i₁ c = siegelGL i₀ i₁ c') : c = c' := by
  have e := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (Sum.inl i₀) (Sum.inr i₁)) h
  simpa [coe_siegelGL, siegelMat, siegelS, h01, Ne.symm h01] using e

variable [CharP K 2]

theorem scalars_subgroupOf_omegaPlus_eq_bot {m : ℕ} (hm : 1 ≤ m) :
    (LargeEvenScalars (Fin m ⊕ Fin m) K).subgroupOf (LargeEvenOmega (LargeEvenQPlus K m)) = ⊥ :=
  scalars_subgroupOf_omega_eq_bot (largeEvenQPlus_smul m)
    (v₀ := Pi.single (Sum.inl ⟨0, hm⟩) 1 + Pi.single (Sum.inr ⟨0, hm⟩) 1)
    (by rw [largeEvenQPlus_single_add_single]; exact one_ne_zero)

theorem scalars_subgroupOf_omegaMinus_eq_bot {m : ℕ} (b c : K) :
    (LargeEvenScalars (LargeEvenMinusIdx m) K).subgroupOf
      (LargeEvenOmega (LargeEvenQMinus m b c)) = ⊥ :=
  scalars_subgroupOf_omega_eq_bot (largeEvenQMinus_smul m b c)
    (v₀ := Pi.single (Sum.inr 0) 1) (by simp [LargeEvenQMinus])

omit [CharP K 2] in
theorem exists_zeta [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = p ∧ ζ ^ p = 1 ∧ ζ ≠ 1 ∧ ζ * ζ ≠ 1 := by
  have := Fact.mk hp
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = p :=
    exists_prime_orderOf_dvd_card' p (by rw [Nat.card_units]; exact hpq)
  refine ⟨ζ, hζo, by rw [← hζo]; exact pow_orderOf_eq_one ζ, ?_, ?_⟩
  · rintro rfl
    rw [orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  · intro h
    have h2 : ζ ^ 2 = 1 := by rw [sq]; exact h
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hζo] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

theorem exists_not_commute_omegaPlus {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (hp : Odd p) {m : ℕ} (hm : 2 ≤ m) :
    ∃ x y : LargeEvenOmega (LargeEvenQPlus K m), x * y ≠ y * x := by
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  refine ⟨⟨siegelGL i₀ i₁ 1, siegelGL_mem_omegaPlus hζ hζ1 h01 1⟩,
    ⟨spTorusGL hζ (Pi.mulSingle i₀ (Multiplicative.ofAdd 1)), spTorusGL_mem_omegaPlus hζ hp _⟩,
    fun h => hζ1 ?_⟩
  have h' : siegelGL i₀ i₁ (1 : K) * spTorusGL hζ (Pi.mulSingle i₀ (Multiplicative.ofAdd 1)) =
      spTorusGL hζ (Pi.mulSingle i₀ (Multiplicative.ofAdd 1)) * siegelGL i₀ i₁ 1 :=
    congrArg Subtype.val h
  have hconj := diagGL_pairedUnits_conj_siegelGL (fun l => zmodPowHom hζ
    ((Pi.mulSingle i₀ (Multiplicative.ofAdd (1 : ZMod p)) : Fin m → Multiplicative (ZMod p)) l))
    i₀ i₁ (1 : K)
  rw [← spTorusGL_apply, ← h', mul_inv_cancel_right, zmodPowHom_mulSingle_self hζ i₀,
    zmodPowHom_mulSingle_of_ne hζ h01, Units.val_one, mul_one, mul_one] at hconj
  exact Units.ext (siegelGL_injective h01 hconj).symm

theorem center_omegaPlus_eq_bot [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {m : ℕ} (hm : 3 ≤ m) :
    Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) = ⊥ := by
  have : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus hm
  obtain ⟨ζ, -, hζ, hζ1, -⟩ := exists_zeta (K := K) hp hp2 hpq
  obtain ⟨x, y, hxy⟩ := exists_not_commute_omegaPlus hζ hζ1 (hp.odd_of_ne_two hp2)
    (by omega : 2 ≤ m)
  set e := projMkEquiv (scalars_subgroupOf_omegaPlus_eq_bot (K := K) (by omega : 1 ≤ m))
  refine center_eq_bot_of_simple (x := e x) (y := e y) fun h => hxy (e.injective ?_)
  rw [map_mul, map_mul, h]

theorem center_omegaMinus_eq_bot [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {m : ℕ} (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) = ⊥ := by
  have hs : IsSimpleGroup (LowTwoRank.StatedProj (LowTwoRank.StatedOmega
      (LowTwoRank.StatedQuadMinus (m + 1) K b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus (by omega) hirr
  have : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    (omegaMinusProjEquiv (m + 1) b c).isSimpleGroup
  obtain ⟨ζ, -, hζ, hζ1, -⟩ := exists_zeta (K := K) hp hp2 hpq
  obtain ⟨x, y, hxy⟩ := exists_not_commute_omegaPlus hζ hζ1 (hp.odd_of_ne_two hp2)
    (by omega : 2 ≤ m)
  set e := projMkEquiv (scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := m) b c)
  set x' : LargeEvenOmega (LargeEvenQMinus m b c) :=
    ⟨blockInl (x : GL (Fin m ⊕ Fin m) K), blockInl_mem_omegaMinus b c x.2⟩
  set y' : LargeEvenOmega (LargeEvenQMinus m b c) :=
    ⟨blockInl (y : GL (Fin m ⊕ Fin m) K), blockInl_mem_omegaMinus b c y.2⟩
  have hinj : Function.Injective (blockInl (K := K) (m := m)) := by
    intro g g' h
    apply Units.ext
    have := congrArg (fun g : GL (LargeEvenMinusIdx m) K =>
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K).toBlocks₁₁) h
    simpa [coe_blockInl] using this
  refine center_eq_bot_of_simple (x := e x') (y := e y') fun h => hxy ?_
  have h1 : x' * y' = y' * x' := e.injective (by rw [map_mul, map_mul, h])
  have h2 : blockInl ((x * y : LargeEvenOmega (LargeEvenQPlus K m)) : GL (Fin m ⊕ Fin m) K) =
      blockInl ((y * x : LargeEvenOmega (LargeEvenQPlus K m)) : GL (Fin m ⊕ Fin m) K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val h1
  exact Subtype.ext (hinj h2)

end Center

end TableBOrth

end CFSG.StandardType
