module

public import CFSG.LocalAnalysis.SteinbergSFOddSymplecticRootCentralizer
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraph
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityUnitary
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent

public noncomputable section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OddLinearRoot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ClassicalGroups.UnitaryFlag

section Tools

theorem nonempty_quotient_ker {G H Q : Type*} [Group G] [Group H] [Group Q] (ψ : G →* H)
    {X : Subgroup H} (h : ψ.range = X) (eX : X ≃* Q) : Nonempty (G ⧸ ψ.ker ≃* Q) :=
  ⟨(QuotientGroup.quotientKerEquivRange ψ).trans ((MulEquiv.subgroupCongr h).trans eX)⟩

theorem false_of_orderOf_four {G : Type*} [Group G] {X : Subgroup G} {y : G} (hy : y ∈ X)
    (hyo : orderOf y = 4) {K : Type*} [Field K] (h2 : (2 : K) = 0)
    (eX : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False :=
  SteinbergCD.SL_two_orderOf_ne_four h2 (eX ⟨y, hy⟩)
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hyo])

theorem apply_eq_of_conj_commute {P : Type*} [Group P] (hZ : center P = ⊥) (β : MulAut P)
    {x : P} (h : MulAut.conj x * β = β * MulAut.conj x) : β x = x := by
  apply OddClassSelector.conj_injective hZ
  rw [← mulAut_mul_conj_mul_inv, ← h, mul_inv_cancel_right]

variable {F : Type} [Field F] {d : ℕ}

theorem apply_eq_smul_of_basisMatrixEquiv_eq {g : (Fin d → F) ≃ₗ[F] (Fin d → F)} {c : Fˣ}
    (h : CatalogueBAlternatingIsometry.basisMatrixEquiv (Pi.basisFun F (Fin d)) g =
      GeneralLinearGroup.scalar (Fin d) c) (v : Fin d → F) : g v = (c : F) • v := by
  have h1 := congrArg (fun A : GL (Fin d) F => (A : Matrix (Fin d) (Fin d) F)) h
  simp only [CatalogueBAlternatingIsometry.basisMatrixEquiv_val, GeneralLinearGroup.coe_scalar,
    LinearMap.toMatrix_eq_toMatrix'] at h1
  have h2 := LinearMap.toMatrix'_mulVec (g : (Fin d → F) →ₗ[F] (Fin d → F)) v
  rw [h1, LinearEquiv.coe_coe] at h2
  rw [← h2]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem conjAut_orderOf_eq_four [Finite F] (hd : 3 ≤ d) {R : GL (Fin d) F} (hR4 : R ^ 4 = 1)
    (hR2 : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin d) c ≠ R ^ 2) :
    orderOf (conjAut d F R) = 4 :=
  SteinbergCD.orderOf_eq_four (by rw [← map_pow, hR4, map_one]) fun h => by
    rw [← map_pow] at h
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hd _).mp h
    exact hR2 c hc

theorem rot_pow_four_and_not_scalar (h2 : (2 : F) ≠ 0) (hd : 3 ≤ d) :
    (SpecialLinearGroup.toGL (SteinbergBT.rotSL (F := F) (d := d) (by omega))) ^ 4 = 1 ∧
      ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin d) c ≠
        (SpecialLinearGroup.toGL (SteinbergBT.rotSL (F := F) (d := d) (by omega))) ^ 2 := by
  refine ⟨by rw [← map_pow, SteinbergBT.rotSL_pow_four, map_one], fun c hc => ?_⟩
  rw [← map_pow] at hc
  have h1 := congrArg
    (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F) ⟨0, by omega⟩ ⟨0, by omega⟩) hc
  have h3 := congrArg
    (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F) ⟨2, by omega⟩ ⟨2, by omega⟩) hc
  simp only [GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix,
    SteinbergBT.coe_rotSL_sq] at h1 h3
  rw [SteinbergBT.rot_sq_apply_left (Fin.ne_of_val_ne (by simp))] at h1
  rw [SteinbergBT.rot_sq_apply_other (Fin.ne_of_val_ne (by simp))
    (Fin.ne_of_val_ne (by simp))] at h3
  simp only [scalar_apply, diagonal_apply_eq] at h1 h3
  apply h2
  linear_combination h1 - h3

end Tools

section Inner

variable {F : Type} [Field F] [Finite F] {d : ℕ}

theorem inner_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 3 ≤ d) {β : MulAut (projectiveSL d F)} {B : GL (Fin d) F}
    (hβB : β = conjAut d F B) (hβ1 : β ≠ 1) (hβ2 : β ^ 2 = 1)
    {X : Subgroup (MulAut (projectiveSL d F))}
    (hX : CFSG.Assembly.IsComponentOf X (inner (projectiveSL d F) ⊓ centralizer {β}))
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eX : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  subst hβB
  have : CharP F ℓ := finite_field_prime_power_characteristic hℓ he hF
  have hk2 : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hk2
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨μ, hμ⟩ := (conjAut_eq_one_iff hd (B ^ 2)).mp (by rw [map_pow, hβ2])
  have hB1 : ∀ c : Fˣ, B ≠ GeneralLinearGroup.scalar (Fin d) c := by
    rintro c rfl
    exact hβ1 (conjAut_scalar c)
  obtain ⟨hXh, hmap, -⟩ := inner_component_lift hd B hX
  set Xh := ⁅X.comap (conjAut d F), X.comap (conjAut d F)⁆
  by_cases hμs : IsSquare μ.val
  ·
    obtain ⟨r₀, hr₀⟩ := hμs
    have hr0 : r₀ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr₀
      exact μ.ne_zero hr₀
    set c₀ : Fˣ := Units.mk0 r₀ hr0
    have hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin d) (c₀ ^ 2) := by
      rw [← hμ]
      congr 1
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hr₀, sq]
    obtain ⟨r, hr2, ⟨eXh⟩, hXi⟩ := square_component_sl hd htwo hsq hB1 hXh
    set ψ : Matrix.SpecialLinearGroup (Fin r) F →* MulAut (projectiveSL d F) :=
      (conjAut d F).comp (Xh.subtype.comp eXh.symm.toMonoidHom) with hψ
    have hψi : Function.Injective ψ := hXi.comp eXh.symm.injective
    have hψr : ψ.range = X := by
      rw [hψ, MonoidHom.range_comp, MonoidHom.range_comp,
        MonoidHom.range_eq_top.mpr eXh.symm.surjective, Subgroup.map_top,
        Subgroup.range_subtype, hmap]
    obtain ⟨φ⟩ := nonempty_quotient_ker ψ hψr eX
    have hker : ψ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ψ).mpr hψi
    obtain ⟨-, -, -, -, hc2, -⟩ := SteinbergBT.linear_scalar_quotient_SL2 hodd hn K hK hr2 ψ.ker
      (by rw [hker]; exact bot_le) φ
    rw [hker, Subgroup.card_bot] at hc2
    omega
  ·
    have : Fact (¬ IsSquare μ.val) := ⟨hμs⟩
    have hsq := hμ.symm
    obtain ⟨hd2, hmapE⟩ := nonsquare_component_sl htwo hsq hXh
    let _ := matrixModule B μ hsq
    have : Finite (extension μ.val) :=
      CatalogueBProjectiveInvolution.quadraticExtension_finite μ.val
    have hcardE : Nat.card (extension μ.val) = Nat.card F ^ 2 := by
      let : Fintype F := Fintype.ofFinite F
      let : Fintype (extension μ.val) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F),
        extension_finrank]
    set e₀ := matrixCentralizerQuadraticEquiv B μ hsq
    set ψ := (conjAut d F).comp (nonsquareCover hsq)
    have hσX : ∀ x, nonsquareCover hsq x ∈ Xh := by
      intro x
      have hx : SpecialLinearGroup.toGL x ∈ CatalogueBGeneralLinear.specialLinearRange
          (matrixDimension B μ hsq) (extension μ.val) := ⟨x, rfl⟩
      rw [← hmapE] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : e₀.symm (SpecialLinearGroup.toGL x) = y := by
        rw [← hyx]
        exact MulEquiv.symm_apply_apply _ _
      change ((e₀.symm (SpecialLinearGroup.toGL x) : centralizer {B}) : GL (Fin d) F) ∈ Xh
      rw [this]
      exact hy
    have hψr : ψ.range = X := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        rw [← hmap]
        exact ⟨_, hσX x, rfl⟩
      · intro y hy
        rw [← hmap] at hy
        obtain ⟨g, hg, rfl⟩ := hy
        have hgC : g ∈ centralizer {B} := hXh.1 hg
        have h1 : e₀ ⟨g, hgC⟩ ∈ CatalogueBGeneralLinear.specialLinearRange
            (matrixDimension B μ hsq) (extension μ.val) := by
          rw [← hmapE]
          exact ⟨⟨g, hgC⟩, hg, rfl⟩
        obtain ⟨x, hx⟩ := h1
        refine ⟨x, ?_⟩
        change conjAut d F ((e₀.symm (SpecialLinearGroup.toGL x) : centralizer {B}) :
          GL (Fin d) F) = conjAut d F g
        rw [hx, MulEquiv.symm_apply_apply]
    have hker : ψ.ker ≤ scalars (matrixDimension B μ hsq) (extension μ.val) := by
      intro x hx
      obtain ⟨t, ht⟩ := (conjAut_eq_one_iff hd _).mp hx
      rw [scalars_eq_center]
      exact mem_center_of_nonsquareCover_scalar hsq ht
    obtain ⟨φ⟩ := nonempty_quotient_ker ψ hψr eX
    have hEodd : Odd (Nat.card (extension μ.val)) := by
      rw [hcardE]
      exact hodd.pow
    obtain ⟨-, h5, -⟩ := SteinbergBT.linear_scalar_quotient_SL2 hEodd hn K hK hd2 ψ.ker hker φ
    rw [hcardE] at h5
    have h3 : Nat.card F ≤ 2 := by nlinarith
    have h4 : Nat.card F ^ 2 ≤ 4 := by nlinarith
    omega

end Inner

section Field

variable {F : Type} [Field F] [Finite F] {d : ℕ}

theorem field_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 3 ≤ d) {β : MulAut (projectiveSL d F)} {B : GL (Fin d) F}
    {σ : F ≃+* F} (hσ : σ ≠ 1) (hβB : β = conjAut d F B * fieldAut d F σ) (hβ2 : β ^ 2 = 1)
    {X : Subgroup (MulAut (projectiveSL d F))}
    (hX : CFSG.Assembly.IsComponentOf X (inner (projectiveSL d F) ⊓ centralizer {β}))
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eX : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  subst hβB
  obtain ⟨heven, hσx, H, hH⟩ := linear_field_involution_descent hℓ he hF hd B σ hσ hβ2
  obtain ⟨-, ⟨e₁, -⟩, hNinn, -, hNC, hNnormal, hCN⟩ :=
    linear_quadratic_field_full_centralizer_rigidity σ (n := d) hd
  set χ := conjAut d F H
  set β₀ := fieldAut d F σ
  set N := (subfieldConj d σ).range with hNdef
  have hY : (inner (projectiveSL d F) ⊓ centralizer {conjAut d F B * fieldAut d F σ}).map
      (MulAut.conj χ⁻¹).toMonoidHom = inner (projectiveSL d F) ⊓ centralizer {β₀} := by
    rw [map_conj_inner_inf_centralizer, hH]
    congr 3
    group
  set X₀ := X.map (MulAut.conj χ⁻¹).toMonoidHom with hX₀def
  have hX₀ : CFSG.Assembly.IsComponentOf X₀ (inner (projectiveSL d F) ⊓ centralizer {β₀}) := by
    have := isComponentOf_map_conj hX χ⁻¹
    rwa [hY] at this
  have := finite_mulAut_projectiveSL (k := F) d
  have hX₀N : CFSG.Assembly.IsComponentOf X₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hX₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β₀ i j).eq
  have : IsSimpleGroup (projectiveSL d (fixedField F σ)) := isSimpleGroup_projectiveSL hd
  have hNs : IsSimpleGroup N := e₁.symm.isSimpleGroup
  have hX₀eq : X₀ = N := eq_of_isComponentOf_simple hNs hX₀N
  set ψ := (MulAut.conj χ).toMonoidHom.comp (subfieldConj d σ) with hψ
  have hψr : ψ.range = X := by
    rw [hψ, MonoidHom.range_comp, ← hNdef, ← hX₀eq, hX₀def, map_conj_inv_map_conj]
  have hker : ψ.ker ≤ scalars d (fixedField F σ) := by
    intro x hx
    have h1 : subfieldConj d σ x = 1 :=
      (MulEquiv.map_eq_one_iff (MulAut.conj χ)).mp hx
    have h2 : x ∈ (subfieldConj d σ).ker := h1
    obtain ⟨hk, -⟩ := linear_quadratic_field_full_centralizer_rigidity σ (n := d) hd
    rwa [hk] at h2
  have hσσ : σ ^ 2 = 1 := RingEquiv.ext fun x => by
    have := Fintype.ofFinite F
    rw [pow_two, RingAut.mul_apply, hσx, hσx, ← pow_mul, ← pow_add,
      show e / 2 + e / 2 = e by obtain ⟨r, hr⟩ := heven; omega, ← hF, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have hk₀ : Nat.card (fixedField F σ) = ℓ ^ (e / 2) := by
    have h1 := fixedField_card_square F σ hσσ hσ
    rw [hF, show e = 2 * (e / 2) by obtain ⟨r, hr⟩ := heven; omega, pow_mul'] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  have hk₀odd : Odd (Nat.card (fixedField F σ)) := by
    rw [hk₀]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨φ⟩ := nonempty_quotient_ker ψ hψr eX
  obtain ⟨-, -, hd2, -⟩ := SteinbergBT.linear_scalar_quotient_SL2 hk₀odd hn K hK (by omega) ψ.ker
    hker φ
  omega

theorem graph_field_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 3 ≤ d) {β : MulAut (projectiveSL d F)} {B : GL (Fin d) F}
    {σ : F ≃+* F} (hσ : σ ≠ 1) (hβB : β = conjAut d F B * fieldAut d F σ * dualAut d F)
    (hβ2 : β ^ 2 = 1) {X : Subgroup (MulAut (projectiveSL d F))}
    (hX : CFSG.Assembly.IsComponentOf X (inner (projectiveSL d F) ⊓ centralizer {β}))
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eX : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  subst hβB
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP F ℓ := finite_field_prime_power_characteristic hℓ he hF
  have hk2 : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hk2
  obtain ⟨heven, hσx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent hℓ he hF hd B σ hσ hβ2
  have hg : 1 ≤ e / 2 := by obtain ⟨r, hr⟩ := heven; omega
  have hKe : Nat.card F = ℓ ^ (2 * (e / 2)) := by
    rw [hF]
    congr 1
    obtain ⟨r, hr⟩ := heven
    omega
  have hud : UnitaryFieldData ℓ (e / 2) F := ⟨hℓ, hg, hKe⟩
  have hσbar : ∀ x, σ x = hud.bar x := fun x => by rw [hσx, hud.bar_apply]
  obtain ⟨-, ⟨ι, -⟩, hNinn, -, hNC, hNnormal, hCN⟩ :=
    linear_graph_field_full_centralizer_rigidity hud (n := d) hd σ hσbar
  set χ := conjAut d F H
  set β₀ := fieldAut d F σ * dualAut d F
  set N := (unitarySU ℓ (e / 2) F d).map (conjAut d F)
  have hY : (inner (projectiveSL d F) ⊓
      centralizer {conjAut d F B * fieldAut d F σ * dualAut d F}).map
        (MulAut.conj χ⁻¹).toMonoidHom = inner (projectiveSL d F) ⊓ centralizer {β₀} := by
    rw [map_conj_inner_inf_centralizer, hH]
    congr 3
    group
  set X₀ := X.map (MulAut.conj χ⁻¹).toMonoidHom with hX₀def
  have hX₀ : CFSG.Assembly.IsComponentOf X₀ (inner (projectiveSL d F) ⊓ centralizer {β₀}) := by
    have := isComponentOf_map_conj hX χ⁻¹
    rwa [hY] at this
  have := finite_mulAut_projectiveSL (k := F) d
  have hX₀N : CFSG.Assembly.IsComponentOf X₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hX₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β₀ i j).eq
  have hK2 : Nat.card F = (ℓ ^ (e / 2)) ^ 2 := by rw [hKe, ← pow_mul, mul_comm]
  have hnq : (d, ℓ ^ (e / 2)) ≠ (3, 2) := fun h => by
    have h2 := congrArg Prod.snd h
    simp only at h2
    have : ℓ ∣ 2 := by
      rw [← h2]
      exact dvd_pow_self ℓ (by omega)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this)
  have : IsSimpleGroup (StatedProj (StatedSU d (ℓ ^ (e / 2)) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F ℓ (e / 2) hK2 d hd hnq
  have : IsSimpleGroup (unitaryPSU hud d) := (unitaryPSUEquiv hud (by omega)).isSimpleGroup
  have hNs : IsSimpleGroup N := ι.symm.isSimpleGroup
  have hX₀eq : X₀ = N := eq_of_isComponentOf_simple hNs hX₀N
  obtain ⟨hR4, hR2⟩ := rot_pow_four_and_not_scalar (F := F) htwo hd
  set R := SpecialLinearGroup.toGL (SteinbergBT.rotSL (F := F) (d := d) (by omega))
  have hRU : R ∈ unitarySU ℓ (e / 2) F d := by
    rw [mem_unitarySU_iff hud]
    refine ⟨(SteinbergBT.rotSL (F := F) (d := d) (by omega)).2, ?_⟩
    change ((SteinbergBT.rotMatrix ⟨0, by omega⟩ ⟨1, by omega⟩).map hud.bar)ᵀ *
      SteinbergBT.rotMatrix (F := F) ⟨0, by omega⟩ ⟨1, by omega⟩ = 1
    rw [SteinbergBT.rotMatrix_map, SteinbergBT.rotMatrix_transpose_mul (Fin.ne_of_val_ne (by simp))]
  have hyX : MulAut.conj χ (conjAut d F R) ∈ X := by
    rw [← map_conj_inv_map_conj χ X, ← hX₀def, hX₀eq]
    exact ⟨conjAut d F R, ⟨R, hRU, rfl⟩, rfl⟩
  exact false_of_orderOf_four hyX
    (by rw [MulEquiv.orderOf_eq, conjAut_orderOf_eq_four hd hR4 hR2])
    (SteinbergBT.two_eq_zero_of_card (by omega) hK) eX

end Field

section Graph

variable {F : Type} [Field F] [Finite F] {d : ℕ}

theorem alternating_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 3 ≤ d) {B : GL (Fin d) F}
    (hB : (B : Matrix (Fin d) (Fin d) F)ᵀ = -B) {X : Subgroup (MulAut (projectiveSL d F))}
    (hX : CFSG.Assembly.IsComponentOf X
      (inner (projectiveSL d F) ⊓ centralizer {conjAut d F B * dualAut d F}))
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eX : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : CharP F ℓ := finite_field_prime_power_characteristic hℓ he hF
  have hk2 : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift hd B hX
  set Xh := ⁅X.comap (conjAut d F), X.comap (conjAut d F)⁆
  set R : GL (Fin d) F := B⁻¹ with hRdef
  set O := CatalogueBGraphForm.isometryGroup d F R
  have hR : (R : Matrix (Fin d) (Fin d) F)ᵀ = -R := by
    have hBR : (B : Matrix (Fin d) (Fin d) F) * R = 1 := by
      rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hRt : (R : Matrix (Fin d) (Fin d) F)ᵀ * (B : Matrix (Fin d) (Fin d) F)ᵀ = 1 := by
      rw [← transpose_mul, hBR, transpose_one]
    calc (R : Matrix (Fin d) (Fin d) F)ᵀ = (R : Matrix (Fin d) (Fin d) F)ᵀ * (B * R) := by
          rw [hBR, Matrix.mul_one]
      _ = -(((R : Matrix (Fin d) (Fin d) F)ᵀ * (B : Matrix (Fin d) (Fin d) F)ᵀ) * R) := by
          rw [hB, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, neg_neg]
      _ = -R := by rw [hRt, Matrix.one_mul]
  set C := CatalogueBLinearHigherB.matrixForm R
  have hCalt := CatalogueBLinearHigherB.matrixForm_isAlt hk2 R hR
  have hCnd := CatalogueBLinearHigherB.matrixForm_nondegenerate R
  set eI := CatalogueBLinearHigherB.isometryGroupEquiv R
  set Y := Xh.subgroupOf O with hYdef
  have hY : CFSG.IsComponent Y := (isComponentOf_iff_isComponent_subgroupOf hXh.1).mp hXh
  set ψ : Y →* MulAut (projectiveSL d F) := (conjAut d F).comp (O.subtype.comp Y.subtype)
    with hψ
  have hψr : ψ.range = X := by
    rw [hψ, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype, hYdef,
      map_subgroupOf_eq_of_le hXh.1, hmap]
  have hA : ∀ a ∈ ψ.ker, ∃ c : F, ∀ w, ((eI.symm (a : O) :
      CatalogueBAlternatingIsometry.isometryGroup C) : (Fin d → F) ≃ₗ[F] (Fin d → F)) w =
        c • w := by
    intro a ha
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hd _).mp ha
    have h1 : CatalogueBAlternatingIsometry.basisMatrixEquiv (Pi.basisFun F (Fin d))
        ((eI.symm (a : O) : CatalogueBAlternatingIsometry.isometryGroup C) :
          (Fin d → F) ≃ₗ[F] (Fin d → F)) = ((a : O) : GL (Fin d) F) := by
      change ((eI (eI.symm (a : O)) : O) : GL (Fin d) F) = _
      rw [MulEquiv.apply_symm_apply]
    exact ⟨c, apply_eq_smul_of_basisMatrixEquiv_eq (h1.trans hc.symm)⟩
  obtain ⟨φ⟩ := nonempty_quotient_ker ψ hψr eX
  obtain ⟨hd2, -, -⟩ := sp_component_quotient hodd hCalt hCnd
    (by rw [Module.finrank_fin_fun]; omega) eI.symm hY ψ.ker hA hn hK φ
  rw [Module.finrank_fin_fun] at hd2
  omega

end Graph

end OddLinearRoot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag

end CFSG.LocalAnalysis.SymplecticFourStandard
