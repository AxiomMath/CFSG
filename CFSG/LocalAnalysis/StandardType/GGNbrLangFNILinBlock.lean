module

public import CFSG.LocalAnalysis.StandardType.GGE0PSLComp
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNILinFactor
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2LinBlock
import CFSG.Quasithin.Background.F918Z2Core
import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedSL)
open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.StandardType.LinNonsplit
open scoped commutatorElement


private theorem l02qfnb_map_mem_commutant {N : ℕ} {K : Type} [Field K]
    (M : Matrix (Fin N) (Fin N) K) (σ : K ≃+* K) {μ : K} (hμ : M.map σ = μ • M)
    (hμ0 : μ ≠ 0) {X : Matrix (Fin N) (Fin N) K} (hX : X * M = M * X) :
    (X.map σ) * M = M * (X.map σ) := by
  have h : (X.map σ) * (μ • M) = (μ • M) * (X.map σ) := by
    rw [← hμ, ← Matrix.map_mul, ← Matrix.map_mul, hX]
  have h2 : μ • ((X.map σ) * M) = μ • (M * (X.map σ)) := by
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using h
  ext i j
  have hij := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  exact mul_left_cancel₀ hμ0 hij

private theorem l02qfnb_ne_zero_of_map_eq_smul {N : ℕ} {K : Type} [Field K]
    (hN : 0 < N) (M : (Matrix (Fin N) (Fin N) K)ˣ) {σ : K ≃+* K} {μ : K}
    (hμ : (M : Matrix (Fin N) (Fin N) K).map σ = μ • (M : Matrix (Fin N) (Fin N) K)) :
    μ ≠ 0 := by
  intro h0
  rw [h0, zero_smul] at hμ
  have hM0 : (M : Matrix (Fin N) (Fin N) K) = 0 := by
    ext i j
    have := congrFun (congrFun hμ i) j
    simpa using this
  have h1 : (M : Matrix (Fin N) (Fin N) K) * ((M⁻¹ : (Matrix (Fin N) (Fin N) K)ˣ) :
      Matrix (Fin N) (Fin N) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h01 : (0 : Matrix (Fin N) (Fin N) K) = 1 := by
    rw [hM0, zero_mul] at h1
    exact h1
  have := congrFun (congrFun h01 ⟨0, hN⟩) ⟨0, hN⟩
  simpa using this

private noncomputable def l02qfnb_statedSLCenterQuotEquivProjective {m : ℕ} {E : Type} [Field E] :
    StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL m E :=
  (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq m)).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center m E)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)).symm

private theorem l02qfnb_statedSLCenterQuotEquivProjective_mk {m : ℕ} {E : Type} [Field E]
    (l : StatedSL m E) :
    l02qfnb_statedSLCenterQuotEquivProjective (m := m) (E := E) (QuotientGroup.mk l) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m E
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  rw [l02qfnb_statedSLCenterQuotEquivProjective]
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem l02qfnb_projMk_eq_iff {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (x y : ↥H) :
    LargeEvenProjMk H x = LargeEvenProjMk H y ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = (x : GL ι K)⁻¹ * (y : GL ι K) := by
  rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range

private theorem l02qfnb_ker_projMk_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) : (LargeEvenProjMk H).ker ≤ Subgroup.center ↥H := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : LargeEvenProjMk H x = LargeEvenProjMk H 1 := by rw [hx, map_one]
  obtain ⟨c, hc⟩ := (l02qfnb_projMk_eq_iff H x 1).mp hx'
  have hxG : (x : GL ι K) = Matrix.GeneralLinearGroup.scalar ι c⁻¹ := by
    have : (x : GL ι K)⁻¹ = Matrix.GeneralLinearGroup.scalar ι c := by simpa using hc.symm
    rw [map_inv, ← this, inv_inv]
  have hxZ : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c⁻¹, hxG.symm⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.1 hxZ (y : GL ι K)

private theorem l02qfnb_data {N : ℕ} {K : Type} [Field K] [Finite K] (M : GL (Fin N) K)
    (hord : (orderOf M : K) ≠ 0) (C : Subgroup (GL (Fin N) K))
    (hC : CFSG.Open.IsComponentOf C
      (Subgroup.centralizer ({M} : Set (GL (Fin N) K)) ⊓ StatedSL N K)) :
    ∃ (r : ℕ) (D : Fin r → Type) (d : Fin r → ℕ) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (_ : ∀ i, Algebra K (D i))
      (Φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[K] Matrix (Fin N) (Fin N) K)
      (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin N) K),
      (∀ i, 1 ≤ d i) ∧ Function.Injective Φ ∧
      (∀ X : Matrix (Fin N) (Fin N) K, X ∈ Set.range Φ ↔
        ∀ g ∈ Subgroup.zpowers M,
          X * (g : Matrix (Fin N) (Fin N) K) = (g : Matrix (Fin N) (Fin N) K) * X) ∧
      Function.Injective θ ∧ θ.range = Subgroup.centralizer ({M} : Set (GL (Fin N) K)) ∧
      (∀ w, ((θ w : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        Φ (fun i => ((w i : GL (Fin (d i)) (D i)) :
          Matrix (Fin (d i)) (Fin (d i)) (D i)))) ∧
      ∃ i : Fin r, 2 ≤ d i ∧
        C = ((StatedSL (d i) (D i)).map
          (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)).map θ := by
  classical
  have hA : (Nat.card (Subgroup.zpowers M) : K) ≠ 0 := by
    rw [Nat.card_zpowers]
    exact hord
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, hNZ, hΦinj, hΦrange, hθinj, hθrange, hθapply⟩ :=
    exists_piMat_commutant (Subgroup.zpowers M) hA
  letI : ∀ i, Field (D i) := hFld
  haveI : ∀ i, Finite (D i) := hFin
  have hcent : Subgroup.centralizer ((Subgroup.zpowers M : Subgroup (GL (Fin N) K)) :
      Set (GL (Fin N) K)) = Subgroup.centralizer ({M} : Set (GL (Fin N) K)) := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg _ (Subgroup.mem_zpowers _)
    · intro hg h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute M g := hg M (Set.mem_singleton M)
      exact (hc.zpow_left k).eq
  have hSL' : ∀ (d : ℕ) (L : Type) [Field L] [Finite L] (X : Subgroup (StatedSL d L)),
      CFSG.Open.IsComponentOf X ⊤ → X = ⊤ :=
    CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds
  have hCeq : Subgroup.centralizer ({M} : Set (GL (Fin N) K)) ⊓ StatedSL N K =
      ((StatedSL N K).comap θ).map θ := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hxr : x ∈ θ.range := by
        rw [hθrange, hcent]
        exact hx1
      obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hxr
      exact Subgroup.mem_map.mpr ⟨w, hx2, rfl⟩
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨?_, hw⟩
      rw [← hcent, ← hθrange]
      exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
  have hCle : C ≤ θ.range := by
    intro x hx
    have hx1 := (hC.1 hx).1
    rw [hθrange, hcent]
    exact hx1
  have hCmap : (C.comap θ).map θ = C := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hCle
  have hC'comp : CFSG.Open.IsComponentOf (C.comap θ) ((StatedSL N K).comap θ) := by
    refine isComponentOf_of_map_injective θ hθinj ?_
    rw [hCmap, ← hCeq]
    exact hC
  have hC'top : CFSG.Open.IsComponentOf (C.comap θ) ⊤ :=
    isComponentOf_top_of_normal' hC'comp
  obtain ⟨i, hi⟩ := exists_factor_of_isComponentOf_top (H := fun k => GL (Fin (d k)) (D k)) hC'top
  have hcommS : ∀ a b : GL (Fin (d i)) (D i), ⁅a, b⁆ ∈ StatedSL (d i) (D i) :=
    fun a b => commutatorElement_mem_statedSL a b
  have hms : Function.Injective (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    intro a b hab
    have := congrFun hab i
    simpa [MonoidHom.mulSingle_apply] using this
  have hC'T : C.comap θ ≤ (StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    have h1 := commutator_eq_self_of_isComponentOf_top hC'top
    have h2 := Subgroup.commutator_mono hi hi
    rw [h1] at h2
    exact h2.trans (commutator_factorSub_le (H := fun k => GL (Fin (d k)) (D k))
      (StatedSL (d i) (D i)) hcommS)
  have hTeq : C.comap θ = (StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    have hX : CFSG.Open.IsComponentOf ((C.comap θ).subgroupOf _) ⊤ :=
      CFSG.ComponentClassification.LocalComponents.of_overgroup hC'top hC'T
    let e : ↥((StatedSL (d i) (D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i)) ≃*
        ↥(StatedSL (d i) (D i)) :=
      (Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
        (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) hms).symm
    have hXe := (CFSG.ComponentClassification.LocalComponents.equiv_iff e _).2 hX
    have htop := hSL' (d i) (D i) _ hXe
    have hXtop : (C.comap θ).subgroupOf _ = ⊤ := eq_top_of_map_equiv_eq_top e _ htop
    exact le_antisymm hC'T (Subgroup.subgroupOf_eq_top.mp hXtop)
  have hCeq2 : C = (((StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i))).map θ := by
    rw [← hTeq, hCmap]
  have hd2 : 2 ≤ d i := by
    by_contra hlt
    push Not at hlt
    have hall : ∀ a ∈ C, a = 1 := by
      intro a ha
      rw [hCeq2] at ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hy1 := eq_one_of_mem_statedSL_of_le_one (by omega) hy
      rw [hy1, map_one, map_one]
    exact not_isQuasisimple_of_comm
      (fun a b => Subtype.ext (by simp [hall a a.2, hall b b.2])) hC.2.2
  refine ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, ?_, hΦinj, hΦrange, hθinj, hθrange.trans hcent,
    hθapply, ⟨i, hd2, hCeq2⟩⟩
  exact fun k => Nat.succ_le_of_lt (Nat.pos_of_ne_zero (hNZ k).out)

private theorem l02qfnb_map_smul_matrix {N : ℕ} {K : Type} [Field K] (σ : K ≃+* K)
    (c : K) (A : Matrix (Fin N) (Fin N) K) :
    (c • A).map σ = (σ c) • A.map σ := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, map_mul]

private theorem l02qfnb_gl_map_val {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (g : GL (Fin n) K) :
    ((Matrix.GeneralLinearGroup.map (σ : K →+* K) g : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K).map σ := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl

private theorem l02qfnb_sl_map_val {n : ℕ} {K : Type} [Field K] (τ : K ≃+* K)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    ((Matrix.SpecialLinearGroup.map (τ : K →+* K) g : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K).map τ := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

private theorem l02qfnb_commute_zpowers {N : ℕ} {K : Type} [Field K] (M : GL (Fin N) K)
    {X : Matrix (Fin N) (Fin N) K}
    (hXM : X * (M : Matrix (Fin N) (Fin N) K) = (M : Matrix (Fin N) (Fin N) K) * X) :
    ∀ g ∈ Subgroup.zpowers M, X * (g : Matrix (Fin N) (Fin N) K) =
      (g : Matrix (Fin N) (Fin N) K) * X := by
  let S : Subgroup (GL (Fin N) K) :=
    { carrier := {g : GL (Fin N) K | X * (g : Matrix (Fin N) (Fin N) K) =
          (g : Matrix (Fin N) (Fin N) K) * X}
      mul_mem' := by
        intro a b ha hb
        have ha' : X * (a : Matrix (Fin N) (Fin N) K) = (a : Matrix (Fin N) (Fin N) K) * X := ha
        have hb' : X * (b : Matrix (Fin N) (Fin N) K) = (b : Matrix (Fin N) (Fin N) K) * X := hb
        change X * ((a * b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
          ((a * b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * X
        rw [Units.val_mul]
        calc X * ((a : Matrix (Fin N) (Fin N) K) * (b : Matrix (Fin N) (Fin N) K))
            = X * (a : Matrix (Fin N) (Fin N) K) * (b : Matrix (Fin N) (Fin N) K) := by
              rw [mul_assoc]
          _ = (a : Matrix (Fin N) (Fin N) K) * X * (b : Matrix (Fin N) (Fin N) K) := by rw [ha']
          _ = (a : Matrix (Fin N) (Fin N) K) * (X * (b : Matrix (Fin N) (Fin N) K)) := by
              rw [mul_assoc]
          _ = (a : Matrix (Fin N) (Fin N) K) * ((b : Matrix (Fin N) (Fin N) K) * X) := by rw [hb']
          _ = ((a : Matrix (Fin N) (Fin N) K) * (b : Matrix (Fin N) (Fin N) K)) * X := by
              rw [mul_assoc]
      one_mem' := by
        change X * ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
          ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * X
        rw [Units.val_one, mul_one, one_mul]
      inv_mem' := by
        intro a ha
        change X * ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
          ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * X
        have hb : ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
            (a : Matrix (Fin N) (Fin N) K) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have hc : (a : Matrix (Fin N) (Fin N) K) *
            ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have h := congrArg (fun Y => ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * Y *
          ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) ha
        have hL : ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
              (X * (a : Matrix (Fin N) (Fin N) K)) *
              ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
            ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * X := by
          rw [← mul_assoc ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) X
                (a : Matrix (Fin N) (Fin N) K),
            mul_assoc (((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * X)
                (a : Matrix (Fin N) (Fin N) K)
                ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K),
            hc, mul_one]
        have hR : ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
              ((a : Matrix (Fin N) (Fin N) K) * X) *
              ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
            X * ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
          rw [← mul_assoc ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
                (a : Matrix (Fin N) (Fin N) K) X, hb, one_mul]
        rw [hL, hR] at h
        exact h.symm }
  exact fun g hg => (Subgroup.zpowers_le.mpr hXM : Subgroup.zpowers M ≤ S) hg

private theorem l02qfnb_mulSingle_eq_single_add {ι : Type} [DecidableEq ι] {A : ι → Type}
    [∀ i, NonAssocRing (A i)] (i : ι) (x : A i) :
    Pi.mulSingle i x = Pi.single i x + (1 - Pi.single i (1 : A i)) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [Pi.mulSingle_eq_same, Pi.single_eq_same]
  · simp [Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h]

private theorem l02qfnb_mul_single_one {ι : Type} [DecidableEq ι] {A : ι → Type}
    [∀ i, NonAssocRing (A i)] (i : ι) (f : ∀ i, A i) :
    f * Pi.single i (1 : A i) = Pi.single i (f i) := by
  ext j
  by_cases h : j = i
  · subst h; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

private theorem l02qfnb_sl_coe {n : ℕ} {K : Type} [Field K]
    (x : Matrix.SpecialLinearGroup (Fin n) K) :
    (((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K x : StatedSL n K) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (x : Matrix (Fin n) (Fin n) K) :=
  CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe n K x

private theorem l02qfnb_sl_symm_coe {n : ℕ} {K : Type} [Field K] (y : StatedSL n K) :
    (((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).symm y :
        Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((y : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe n K
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).symm y)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

private theorem l02qfnb_map_scalar {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (c : K) :
    (Matrix.scalar (Fin n) c).map σ = Matrix.scalar (Fin n) (σ c) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.map_apply, h]

private abbrev l02qfnb_mat {d : ℕ} {E : Type} [Field E] (x : StatedSL d E) :
    Matrix (Fin d) (Fin d) E :=
  ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)

private theorem l02qfnb_conj_scalar {d : ℕ} {F : Type} [Field F] (T : Matrix (Fin d) (Fin d) F)
    (hT : IsUnit T) (c : F) :
    T * (c • (1 : Matrix (Fin d) (Fin d) F)) * T⁻¹ = c • (1 : Matrix (Fin d) (Fin d) F) := by
  have hTinv : T⁻¹ = Units.val ((hT.unit)⁻¹) := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    have h2 : Ring.inverse T = Ring.inverse (hT.unit : Matrix (Fin d) (Fin d) F) := by
      rw [hT.unit_spec]
    rw [h2, Ring.inverse_unit]
  have hTunit : T * T⁻¹ = 1 := by
    rw [hTinv]
    have h1 : (hT.unit : Matrix (Fin d) (Fin d) F) *
        Units.val ((hT.unit)⁻¹) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rwa [hT.unit_spec] at h1
  calc T * (c • (1 : Matrix (Fin d) (Fin d) F)) * T⁻¹
      = c • (T * 1) * T⁻¹ := by rw [Matrix.mul_smul]
    _ = c • T * T⁻¹ := by rw [mul_one]
    _ = c • (T * T⁻¹) := by rw [Matrix.smul_mul]
    _ = c • (1 : Matrix (Fin d) (Fin d) F) := by rw [hTunit]

theorem fniLin_block {N : ℕ} (hN : 2 ≤ N) {K : Type} [Field K] [Finite K] [CharP K 2]
    (M : GL (Fin N) K) (hM : Odd (orderOf M)) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hMσ : ∃ μ : K, (M : Matrix (Fin N) (Fin N) K).map σ = μ • (M : Matrix (Fin N) (Fin N) K))
    (C : Subgroup (GL (Fin N) K))
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({M} : Set (GL (Fin N) K))))
    (hCSL : C ≤ LargeEvenSLGroup (Fin N) K)
    (hσC : ∀ c ∈ C, Matrix.GeneralLinearGroup.map (σ : K →+* K) c ∈ C)
    (J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K)))
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))) :
    ∃ (m : ℕ) (D : Type) (_ : Field D) (_ : Finite D) (_ : CharP D 2)
      (ψ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LinearFlag.projectiveSL m D)
      (B : GL (Fin m) D) (τ : D ≃+* D), 2 ≤ m ∧ τ ≠ 1 ∧
      ∀ (x x' : LargeEvenSLGroup (Fin N) K)
        (hx : LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x ∈ J₀)
        (hx' : LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x' ∈ J₀),
        ((x' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
            ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map σ →
          ψ (QuotientGroup.mk ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x', hx'⟩) =
            LinearFlag.conjAut m D B (LinearFlag.fieldAut m D τ
              (ψ (QuotientGroup.mk ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x, hx⟩))) := by
  classical
  have hord : (orderOf M : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    exact (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr h)
  have hM_comp : CFSG.Open.IsComponentOf C
      (Subgroup.centralizer ({M} : Set (GL (Fin N) K)) ⊓ StatedSL N K) := by
    have hM' : CFSG.Assembly.IsComponentOf C
        (Subgroup.centralizer ({M} : Set (GL (Fin N) K)) ⊓ LargeEvenSLGroup (Fin N) K) :=
      hC.of_le_of_le (le_inf hC.1 hCSL) inf_le_left
    have hM'' : CFSG.Assembly.IsComponentOf C
        (Subgroup.centralizer ({M} : Set (GL (Fin N) K)) ⊓ StatedSL N K) := by
      rwa [CFSG.Assembly.largeEvenSLGroup_eq_statedSL N] at hM'
    exact (CFSG.Assembly.isComponentOf_iff_open).1 hM''
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, hd1, hΦinj, hΦrange, hθinj, hθrange, hθapply,
    i, hd2, hCeq⟩ := l02qfnb_data M hord C hM_comp
  letI : ∀ j, Field (D j) := hFld
  haveI : ∀ j, Finite (D j) := hFin
  letI : ∀ j, Algebra K (D j) := hAlg
  obtain ⟨μ, hμ⟩ := hMσ
  have hμ0 : μ ≠ 0 := l02qfnb_ne_zero_of_map_eq_smul (by omega : 0 < N) M hμ
  let Mσ : Matrix (Fin N) (Fin N) K ≃+* Matrix (Fin N) (Fin N) K :=
    RingEquiv.mapMatrix (m := Fin N) σ
  have hMσ_apply : ∀ A : Matrix (Fin N) (Fin N) K, Mσ A = A.map σ :=
    fun A => RingEquiv.mapMatrix_apply σ A
  have hmap_range : ∀ w : (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)),
      Mσ (Φ w) ∈ Set.range Φ := by
    intro w
    rw [hΦrange]
    intro g hg
    have hXM : (Φ w) * (M : Matrix (Fin N) (Fin N) K) =
        (M : Matrix (Fin N) (Fin N) K) * (Φ w) :=
      (hΦrange (Φ w)).mp ⟨w, rfl⟩ M (Subgroup.mem_zpowers M)
    have hmapM : Mσ (Φ w) * (M : Matrix (Fin N) (Fin N) K) =
        (M : Matrix (Fin N) (Fin N) K) * Mσ (Φ w) := by
      rw [hMσ_apply (Φ w)]
      exact l02qfnb_map_mem_commutant (M : Matrix (Fin N) (Fin N) K) σ hμ hμ0 hXM
    exact l02qfnb_commute_zpowers M hmapM g hg
  let sFun : (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)) →
      (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)) :=
    fun w => Classical.choose (hmap_range w)
  have hsFun_spec : ∀ w, Φ (sFun w) = Mσ (Φ w) := by
    intro w
    exact Classical.choose_spec (hmap_range w)
  let sHom : (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)) →+*
      (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)) :=
    { toFun := sFun
      map_one' := hΦinj (by
        calc Φ (sFun 1) = Mσ (Φ 1) := hsFun_spec 1
          _ = Mσ 1 := by rw [map_one Φ]
          _ = 1 := map_one Mσ
          _ = Φ 1 := (map_one Φ).symm)
      map_mul' := fun a b => hΦinj (by
        calc Φ (sFun (a * b)) = Mσ (Φ (a * b)) := hsFun_spec (a * b)
          _ = Mσ (Φ a * Φ b) := by rw [map_mul Φ]
          _ = Mσ (Φ a) * Mσ (Φ b) := map_mul Mσ (Φ a) (Φ b)
          _ = Φ (sFun a) * Φ (sFun b) := by rw [hsFun_spec a, hsFun_spec b]
          _ = Φ (sFun a * sFun b) := (map_mul Φ (sFun a) (sFun b)).symm)
      map_zero' := hΦinj (by
        calc Φ (sFun 0) = Mσ (Φ 0) := hsFun_spec 0
          _ = Mσ 0 := by rw [map_zero Φ]
          _ = 0 := map_zero Mσ
          _ = Φ 0 := (map_zero Φ).symm)
      map_add' := fun a b => hΦinj (by
        calc Φ (sFun (a + b)) = Mσ (Φ (a + b)) := hsFun_spec (a + b)
          _ = Mσ (Φ a + Φ b) := by rw [map_add Φ]
          _ = Mσ (Φ a) + Mσ (Φ b) := map_add Mσ (Φ a) (Φ b)
          _ = Φ (sFun a) + Φ (sFun b) := by rw [hsFun_spec a, hsFun_spec b]
          _ = Φ (sFun a + sFun b) := (map_add Φ (sFun a) (sFun b)).symm) }
  have hsHom_inj : Function.Injective sHom := by
    intro a b hab
    change sFun a = sFun b at hab
    have h1 : Mσ (Φ a) = Mσ (Φ b) := by
      rw [← hsFun_spec a, ← hsFun_spec b, hab]
    exact hΦinj (Mσ.injective h1)
  haveI : Finite (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)) := inferInstance
  let s : (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)) ≃+*
      (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)) :=
    RingEquiv.ofBijective sHom ⟨hsHom_inj, Finite.injective_iff_surjective.mp hsHom_inj⟩
  have hs_apply : ∀ w, Φ (s w) = (Φ w).map σ :=
    fun w => (hsFun_spec w).trans (hMσ_apply (Φ w))
  have hs_smul : ∀ (c : K) (w : (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j))),
      s (c • w) = σ c • s w := by
    intro c w
    apply hΦinj
    calc Φ (s (c • w)) = (Φ (c • w)).map σ := hs_apply (c • w)
      _ = (c • Φ w).map σ := by rw [map_smul]
      _ = (σ c) • (Φ w).map σ := l02qfnb_map_smul_matrix σ c (Φ w)
      _ = (σ c) • Φ (s w) := by rw [hs_apply w]
      _ = Φ (σ c • s w) := by rw [map_smul]
  let mulI : GL (Fin (d i)) (D i) →* (∀ j, GL (Fin (d j)) (D j)) :=
    MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i
  have hmulI_coe : ∀ (x : StatedSL (d i) (D i)),
      (fun j => (((mulI x) j : GL (Fin (d j)) (D j)) :
          Matrix (Fin (d j)) (Fin (d j)) (D j))) =
        Pi.mulSingle i (l02qfnb_mat x) := by
    intro x
    ext j
    by_cases h : j = i
    · subst h
      simp [mulI, MonoidHom.mulSingle_apply]
    · simp [mulI, MonoidHom.mulSingle_apply, h]
  have hθmulI : ∀ (z : StatedSL (d i) (D i)),
      ((θ (mulI z) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        Φ (Pi.mulSingle i (l02qfnb_mat z)) := by
    intro z
    rw [hθapply, hmulI_coe z]
  have hst : ∀ x : StatedSL (d i) (D i),
      ∃ y : StatedSL (d i) (D i),
        s (Pi.mulSingle i (l02qfnb_mat x)) =
          Pi.mulSingle i (l02qfnb_mat y) := by
    intro x
    have hxC : θ (mulI x) ∈ C := by
      rw [hCeq]
      exact Subgroup.mem_map.mpr ⟨mulI x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩, rfl⟩
    have hσxC : Matrix.GeneralLinearGroup.map (σ : K →+* K) (θ (mulI x)) ∈ C := hσC _ hxC
    have hσxC' : Matrix.GeneralLinearGroup.map (σ : K →+* K) (θ (mulI x)) ∈
        ((StatedSL (d i) (D i)).map mulI).map θ := by rwa [← hCeq]
    obtain ⟨w, hw, hwσ⟩ := Subgroup.mem_map.mp hσxC'
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp hw
    refine ⟨⟨y, hy⟩, ?_⟩
    apply hΦinj
    calc Φ (s (Pi.mulSingle i (l02qfnb_mat x)))
        = (Φ (Pi.mulSingle i (l02qfnb_mat x))).map σ := hs_apply _
      _ = ((θ (mulI x) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map σ := by rw [hθmulI x]
      _ = ((Matrix.GeneralLinearGroup.map (σ : K →+* K) (θ (mulI x)) : GL (Fin N) K) :
            Matrix (Fin N) (Fin N) K) := (l02qfnb_gl_map_val σ (θ (mulI x))).symm
      _ = (θ w : Matrix (Fin N) (Fin N) K) := by rw [hwσ]
      _ = (θ (mulI y) : Matrix (Fin N) (Fin N) K) := by rw [← hyw]
      _ = Φ (Pi.mulSingle i (l02qfnb_mat ⟨y, hy⟩)) := hθmulI ⟨y, hy⟩
  let f : StatedSL (d i) (D i) → StatedSL (d i) (D i) := fun x => Classical.choose (hst x)
  have hf_spec : ∀ x, s (Pi.mulSingle i (l02qfnb_mat x)) =
      Pi.mulSingle i (l02qfnb_mat (f x)) := fun x => Classical.choose_spec (hst x)
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h2 : (Pi.mulSingle i (l02qfnb_mat (f a)) :
        (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j))) =
        Pi.mulSingle i (l02qfnb_mat (f b)) := by
      rw [hab]
    have h1 : (Pi.mulSingle i (l02qfnb_mat a) :
        (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j))) =
        Pi.mulSingle i (l02qfnb_mat b) := by
      apply s.injective
      rw [hf_spec a, hf_spec b, h2]
    apply Subtype.ext
    apply Units.ext
    have := congrFun h1 i
    simpa [l02qfnb_mat, Pi.mulSingle_eq_same] using this
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  have hst' : ∀ x : StatedSL (d i) (D i),
      ∃ y : StatedSL (d i) (D i),
        s.symm (Pi.mulSingle i (l02qfnb_mat x)) =
          Pi.mulSingle i (l02qfnb_mat y) := by
    intro x
    obtain ⟨z, hz⟩ := hf_surj x
    refine ⟨z, ?_⟩
    rw [← hz, ← hf_spec z, RingEquiv.symm_apply_apply]
  have hsSL : ∀ x : Matrix.SpecialLinearGroup (Fin (d i)) (D i),
      ∃ y : Matrix.SpecialLinearGroup (Fin (d i)) (D i),
        s (Pi.mulSingle i (x : Matrix (Fin (d i)) (Fin (d i)) (D i))) =
          Pi.mulSingle i (y : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
    intro x
    obtain ⟨y', hy'⟩ := hst ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)) x)
    refine ⟨(CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)).symm y', ?_⟩
    have hx : l02qfnb_mat ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)) x) =
        (x : Matrix (Fin (d i)) (Fin (d i)) (D i)) := l02qfnb_sl_coe x
    have hy : l02qfnb_mat y' =
        (((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)).symm y' :
          Matrix.SpecialLinearGroup (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      (l02qfnb_sl_symm_coe y').symm
    rw [hx, hy] at hy'
    exact hy'
  have hsSL' : ∀ x : Matrix.SpecialLinearGroup (Fin (d i)) (D i),
      ∃ y : Matrix.SpecialLinearGroup (Fin (d i)) (D i),
        s.symm (Pi.mulSingle i (x : Matrix (Fin (d i)) (Fin (d i)) (D i))) =
          Pi.mulSingle i (y : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
    intro x
    obtain ⟨y', hy'⟩ := hst' ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)) x)
    refine ⟨(CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)).symm y', ?_⟩
    have hx : l02qfnb_mat ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)) x) =
        (x : Matrix (Fin (d i)) (Fin (d i)) (D i)) := l02qfnb_sl_coe x
    have hy : l02qfnb_mat y' =
        (((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)).symm y' :
          Matrix.SpecialLinearGroup (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      (l02qfnb_sl_symm_coe y').symm
    rw [hx, hy] at hy'
    exact hy'
  have hse : s (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) =
      Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
    fniLin_factor_fixed s i hd2 hsSL hsSL'
  have hse_symm : s.symm (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) = Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
    have h := congrArg s.symm hse
    rw [RingEquiv.symm_apply_apply] at h
    exact h.symm
  let s_iFun : Matrix (Fin (d i)) (Fin (d i)) (D i) → Matrix (Fin (d i)) (Fin (d i)) (D i) :=
    fun A => (s (Pi.single i A)) i
  have hs_single : ∀ A : Matrix (Fin (d i)) (Fin (d i)) (D i),
      s (Pi.single i A) = Pi.single i (s_iFun A) := by
    intro A
    have h1 : s (Pi.single i A) * Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) =
        s (Pi.single i A) := by
      calc s (Pi.single i A) * Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))
          = s (Pi.single i A) * s (s.symm (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)))) := by
            rw [RingEquiv.apply_symm_apply]
        _ = s (Pi.single i A * s.symm (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)))) := by
            rw [map_mul]
        _ = s (Pi.single i A * Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
            rw [hse_symm]
        _ = s (Pi.single i A) := by rw [← Pi.single_mul, mul_one]
    have h2 := l02qfnb_mul_single_one i (s (Pi.single i A))
    rw [h1] at h2
    exact h2
  have hs_i_one : s_iFun 1 = 1 := by
    change (s (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)))) i = 1
    rw [hse, Pi.single_eq_same]
  have hs_i_zero : s_iFun 0 = 0 := by
    change (s (Pi.single i (0 : Matrix (Fin (d i)) (Fin (d i)) (D i)))) i = 0
    simp
  have hs_i_add : ∀ A B, s_iFun (A + B) = s_iFun A + s_iFun B := by
    intro A B
    change (s (Pi.single i (A + B))) i = (s (Pi.single i A)) i + (s (Pi.single i B)) i
    rw [Pi.single_add, map_add, Pi.add_apply]
  have hs_i_mul : ∀ A B, s_iFun (A * B) = s_iFun A * s_iFun B := by
    intro A B
    change (s (Pi.single i (A * B))) i = (s (Pi.single i A)) i * (s (Pi.single i B)) i
    rw [Pi.single_mul, map_mul, Pi.mul_apply]
  let s_iHom : Matrix (Fin (d i)) (Fin (d i)) (D i) →+*
      Matrix (Fin (d i)) (Fin (d i)) (D i) :=
    { toFun := s_iFun
      map_one' := hs_i_one
      map_mul' := hs_i_mul
      map_zero' := hs_i_zero
      map_add' := hs_i_add }
  let s_iInv : Matrix (Fin (d i)) (Fin (d i)) (D i) → Matrix (Fin (d i)) (Fin (d i)) (D i) :=
    fun A => (s.symm (Pi.single i A)) i
  have hs_single_symm : ∀ A, s.symm (Pi.single i A) = Pi.single i (s_iInv A) := by
    intro A
    have h1 : s.symm (Pi.single i A) * Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) =
        s.symm (Pi.single i A) := by
      calc s.symm (Pi.single i A) * Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))
          = s.symm (Pi.single i A) * s.symm (s (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)))) := by
            rw [RingEquiv.symm_apply_apply]
        _ = s.symm (Pi.single i A * s (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)))) := by
            rw [map_mul]
        _ = s.symm (Pi.single i A * Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
            rw [hse]
        _ = s.symm (Pi.single i A) := by rw [← Pi.single_mul, mul_one]
    have h2 := l02qfnb_mul_single_one i (s.symm (Pi.single i A))
    rw [h1] at h2
    exact h2
  have hs_i_left : Function.LeftInverse s_iInv s_iFun := by
    intro A
    change (s.symm (Pi.single i (s_iFun A))) i = A
    rw [← hs_single A, RingEquiv.symm_apply_apply, Pi.single_eq_same]
  have hs_i_right : Function.RightInverse s_iInv s_iFun := by
    intro A
    change (s (Pi.single i (s_iInv A))) i = A
    rw [← hs_single_symm A, RingEquiv.apply_symm_apply, Pi.single_eq_same]
  have hs_i_bij : Function.Bijective s_iHom :=
    ⟨fun A B h => by
        change s_iFun A = s_iFun B at h
        have h' := congrArg s_iInv h
        rwa [hs_i_left A, hs_i_left B] at h',
      fun B => ⟨s_iInv B, hs_i_right B⟩⟩
  let s_i : Matrix (Fin (d i)) (Fin (d i)) (D i) ≃+*
      Matrix (Fin (d i)) (Fin (d i)) (D i) := RingEquiv.ofBijective s_iHom hs_i_bij
  have hs_mulSingle : ∀ A, s (Pi.mulSingle i A) = Pi.mulSingle i (s_i A) := by
    intro A
    rw [l02qfnb_mulSingle_eq_single_add (A := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i A, map_add, hs_single A, map_sub, map_one, hse]
    exact (l02qfnb_mulSingle_eq_single_add (A := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i (s_iFun A)).symm
  obtain ⟨τ, T, hT, hconj⟩ :=
    CFSG.Quasithin.SwapModel.exists_conj_of_ringEquiv (F := D i) (d := d i) (by omega) s_i
  have hTinv : T⁻¹ = Units.val ((hT.unit)⁻¹) := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    have h2 : Ring.inverse T = Ring.inverse (hT.unit : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
      rw [hT.unit_spec]
    rw [h2, Ring.inverse_unit]
  have hsingle_alg : ∀ c : K,
      Pi.single i (algebraMap K (D i) c • (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) =
        (c • (1 : (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)))) *
          Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
    intro c
    ext j
    by_cases h : j = i
    · subst h
      simp [Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne h]
  have hs_i_scalar : ∀ c : K,
      s_i (algebraMap K (D i) c • (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) =
        algebraMap K (D i) (σ c) • (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
    intro c
    change (s (Pi.single i (algebraMap K (D i) c •
        (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))))) i =
      algebraMap K (D i) (σ c) • (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))
    rw [hsingle_alg c, map_mul, hs_smul, map_one s, hse, ← hsingle_alg (σ c), Pi.single_eq_same]
  have hτ_alg : ∀ c : K, τ (algebraMap K (D i) c) = algebraMap K (D i) (σ c) := by
    intro c
    have h1 := hconj (algebraMap K (D i) c • (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)))
    rw [hs_i_scalar c] at h1
    have hmap : (algebraMap K (D i) c • (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))).map τ =
        (τ (algebraMap K (D i) c)) • (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
      rw [l02qfnb_map_smul_matrix τ (algebraMap K (D i) c)
        (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))]
      simp
    rw [hmap, l02qfnb_conj_scalar T hT] at h1
    have h2 := congrFun (congrFun h1 (⟨0, by omega⟩ : Fin (d i))) (⟨0, by omega⟩ : Fin (d i))
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
    exact h2.symm
  have hτ_ne : τ ≠ 1 := by
    intro hτ
    apply hσ
    ext c
    have h := hτ_alg c
    rw [hτ] at h
    have h2 : algebraMap K (D i) c = algebraMap K (D i) (σ c) := by simpa using h
    exact (FaithfulSMul.algebraMap_injective K (D i) h2).symm
  have hmulI_inj : Function.Injective mulI := by
    intro a b hab
    have := congrFun hab i
    simpa [mulI, MonoidHom.mulSingle_apply] using this
  let φ : StatedSL (d i) (D i) →* ↥C :=
    { toFun := fun x => ⟨θ (mulI x), by
        rw [hCeq]
        exact Subgroup.mem_map.mpr ⟨mulI x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp [mulI]
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, MonoidHom.map_mul] }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    have h1 : θ (mulI (x : GL (Fin (d i)) (D i))) = θ (mulI (y : GL (Fin (d i)) (D i))) :=
      congrArg Subtype.val hxy
    exact hmulI_inj (hθinj h1)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨c, hc⟩
    have hc' : c ∈ Subgroup.map θ (Subgroup.map mulI (StatedSL (d i) (D i))) := by
      rw [← hCeq]
      exact hc
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hc'
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    show θ (mulI x) = c
    rw [hxy, hyc]
  let e : StatedSL (d i) (D i) ≃* ↥C := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hQ : CFSG.Assembly.IsQuasisimple (StatedSL (d i) (D i)) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e hC.2.2
  have hperf : commutator (StatedSL (d i) (D i)) = ⊤ := hQ.1
  have hperfG : Group.IsPerfect (StatedSL (d i) (D i)) := ⟨hperf⟩
  let πCSL : ↥C →* ↥(LargeEvenSLGroup (Fin N) K) := Subgroup.inclusion hCSL
  let πC : ↥C →* ↥J₀ :=
    { toFun := fun c => ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (πCSL c), by
        rw [hJ₀]
        exact Subgroup.mem_map.mpr ⟨πCSL c, Subgroup.mem_subgroupOf.mpr c.2, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hπC_surj : Function.Surjective πC := by
    rintro ⟨j, hj⟩
    have hj' : j ∈ (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) := by
      rw [← hJ₀]
      exact hj
    obtain ⟨y, hy, hyj⟩ := Subgroup.mem_map.mp hj'
    refine ⟨⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    change LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)
      (πCSL ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩) = j
    have hpc : πCSL ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩ = y := Subtype.ext rfl
    rw [hpc]
    exact hyj
  have hπC_ker : πC.ker ≤ Subgroup.center ↥C := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hc' : πCSL c ∈ (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker := by
      rw [MonoidHom.mem_ker]
      simpa [πC] using congrArg Subtype.val hc
    have hcen := l02qfnb_ker_projMk_le_center (LargeEvenSLGroup (Fin N) K) hc'
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro d
    apply Subtype.ext
    show (πCSL d : GL (Fin N) K) * (πCSL c : GL (Fin N) K) =
      (πCSL c : GL (Fin N) K) * (πCSL d : GL (Fin N) K)
    exact congrArg Subtype.val (hcen (πCSL d))
  let gAB : StatedSL (d i) (D i) →* ↥J₀ := πC.comp φ
  have hgAB_surj : Function.Surjective gAB := hπC_surj.comp hφsurj
  have hker : gAB.ker ≤ Subgroup.center (StatedSL (d i) (D i)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : φ x ∈ πC.ker := by rw [MonoidHom.mem_ker]; exact hx
    have hx2 : φ x ∈ Subgroup.center ↥C := hπC_ker hx1
    rw [Subgroup.mem_center_iff] at hx2 ⊢
    intro y
    apply hφinj
    rw [map_mul, map_mul]
    exact hx2 (φ y)
  let φq : StatedSL (d i) (D i) →* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    (QuotientGroup.mk' (Subgroup.center ↥J₀)).comp gAB
  have hφqsurj : Function.Surjective φq :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J₀)).comp hgAB_surj
  have hcomap : (Subgroup.center ↥J₀).comap gAB =
      Subgroup.center (StatedSL (d i) (D i)) :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperfG gAB hgAB_surj hker
  have hφqker : Subgroup.center (StatedSL (d i) (D i)) = φq.ker := by
    dsimp only [φq]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  let ecent : StatedSL (d i) (D i) ⧸ Subgroup.center (StatedSL (d i) (D i)) ≃*
      ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    QuotientGroup.liftEquiv (Subgroup.center (StatedSL (d i) (D i))) (φ := φq)
      hφqsurj hφqker
  have hecent_mk : ∀ a : StatedSL (d i) (D i),
      ecent (QuotientGroup.mk a) = QuotientGroup.mk (gAB a) :=
    fun a => QuotientGroup.liftEquiv_mk (Subgroup.center (StatedSL (d i) (D i)))
      (φ := φq) hφqsurj hφqker a
  let ψ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (d i) (D i) :=
    ecent.symm.trans (l02qfnb_statedSLCenterQuotEquivProjective (m := d i) (E := D i))
  refine ⟨d i, D i, hFld i, hFin i, charP_of_injective_algebraMap (algebraMap K (D i)).injective 2,
    ψ, hT.unit, τ, hd2, hτ_ne, ?_⟩
  intro x x' hx hx' hxx'
  let eSL := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)
  obtain ⟨a, ha⟩ := hgAB_surj ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x, hx⟩
  have hψa : ψ (QuotientGroup.mk ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x, hx⟩) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (d i) (D i) (eSL.symm a) := by
    change (l02qfnb_statedSLCenterQuotEquivProjective (m := d i) (E := D i))
        (ecent.symm (QuotientGroup.mk ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x, hx⟩)) = _
    have hsymm : ecent.symm (QuotientGroup.mk ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x, hx⟩) =
        QuotientGroup.mk a := by
      rw [← ha, ← hecent_mk a, MulEquiv.symm_apply_apply]
    rw [hsymm]
    exact l02qfnb_statedSLCenterQuotEquivProjective_mk a
  let c0 : ↥C := φ a
  let cSL : LargeEvenSLGroup (Fin N) K := πCSL c0
  have hcSL_gl : (cSL : GL (Fin N) K) = θ (mulI a) := rfl
  have hcSL_proj : LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) cSL =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x := by
    have h := congrArg Subtype.val ha
    change LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) cSL = _ at h
    exact h
  obtain ⟨z, hz⟩ := (l02qfnb_projMk_eq_iff (LargeEvenSLGroup (Fin N) K) cSL x).mp hcSL_proj
  let σu : Kˣ →* Kˣ := Units.map (σ : K →+* K)
  have hx_eq : (x : GL (Fin N) K) = (cSL : GL (Fin N) K) *
      Matrix.GeneralLinearGroup.scalar (Fin N) z := by
    rw [hz, ← mul_assoc, mul_inv_cancel, one_mul]
  have hx'_mat : ((x' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      ((cSL : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map σ *
        Matrix.scalar (Fin N) (σ z) := by
    rw [hxx', hx_eq]
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.map_mul,
      l02qfnb_map_scalar σ (z : K)]
  obtain ⟨y0, hy0⟩ := hst a
  have hs_i_eq : s_i (l02qfnb_mat a) = l02qfnb_mat y0 := by
    have h2 : (Pi.mulSingle i (s_i (l02qfnb_mat a)) :
        (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j))) =
        Pi.mulSingle i (l02qfnb_mat y0) := by
      rw [← hs_mulSingle (l02qfnb_mat a)]
      exact hy0
    exact Pi.mulSingle_injective i h2
  let cSL'' : LargeEvenSLGroup (Fin N) K :=
    ⟨((φ y0 : ↥C) : GL (Fin N) K), hCSL (φ y0).2⟩
  have hcSL'_mat : ((cSL'' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      ((cSL : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map σ := by
    rw [hcSL_gl]
    change (((φ y0 : ↥C) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = _
    calc (((φ y0 : ↥C) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
        = ((θ (mulI y0) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := rfl
      _ = Φ (Pi.mulSingle i (l02qfnb_mat y0)) := hθmulI y0
      _ = Φ (Pi.mulSingle i (s_i (l02qfnb_mat a))) := by rw [← hs_i_eq]
      _ = Φ (s (Pi.mulSingle i (l02qfnb_mat a))) := by
            rw [← hs_mulSingle (l02qfnb_mat a)]
      _ = (Φ (Pi.mulSingle i (l02qfnb_mat a))).map σ := hs_apply _
      _ = ((θ (mulI a) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map σ := by rw [hθmulI a]
  have hx'_gl : (x' : GL (Fin N) K) = (cSL'' : GL (Fin N) K) *
      Matrix.GeneralLinearGroup.scalar (Fin N) (σu z) := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hcSL'_mat]
    exact hx'_mat
  have hproj : LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x' =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) cSL'' := by
    rw [l02qfnb_projMk_eq_iff]
    refine ⟨(σu z)⁻¹, ?_⟩
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin N) ((σu z)⁻¹) =
        (x' : GL (Fin N) K)⁻¹ * (cSL'' : GL (Fin N) K) := by
      rw [map_inv, hx'_gl, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact h1
  obtain ⟨a', ha'⟩ := hgAB_surj ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x', hx'⟩
  have hgAB_eq : gAB y0 = gAB a' := by
    apply Subtype.ext
    have h2 := congrArg Subtype.val ha'
    change LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (πCSL (φ y0)) = (gAB a').val
    rw [h2]
    change LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) cSL'' = _
    exact hproj.symm
  have hmk_eq : (QuotientGroup.mk (y0 : StatedSL (d i) (D i)) :
      StatedSL (d i) (D i) ⧸ Subgroup.center (StatedSL (d i) (D i))) =
      (QuotientGroup.mk a' : StatedSL (d i) (D i) ⧸ Subgroup.center (StatedSL (d i) (D i))) := by
    apply ecent.injective
    rw [hecent_mk, hecent_mk, hgAB_eq]
  have hψa' : ψ (QuotientGroup.mk ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x', hx'⟩) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (d i) (D i) (eSL.symm y0) := by
    change (l02qfnb_statedSLCenterQuotEquivProjective (m := d i) (E := D i))
        (ecent.symm (QuotientGroup.mk ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x', hx'⟩)) = _
    have hsymm : ecent.symm (QuotientGroup.mk ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x', hx'⟩) =
        QuotientGroup.mk (y0 : StatedSL (d i) (D i)) := by
      rw [← ha', ← hecent_mk a', MulEquiv.symm_apply_apply, hmk_eq]
    rw [hsymm]
    exact l02qfnb_statedSLCenterQuotEquivProjective_mk _
  have hsl_eq : eSL.symm y0 =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (d i) (D i) hT.unit
        (Matrix.SpecialLinearGroup.map (τ : D i →+* D i) (eSL.symm a)) := by
    apply Subtype.ext
    rw [l02qfnb_sl_symm_coe y0,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
      l02qfnb_sl_map_val, l02qfnb_sl_symm_coe a, hT.unit_spec, ← hTinv]
    have hs_i_coe : ((y0 : GL (Fin (d i)) (D i)) :
        Matrix (Fin (d i)) (Fin (d i)) (D i)) =
        s_i (((a : GL (Fin (d i)) (D i)) :
          Matrix (Fin (d i)) (Fin (d i)) (D i))) := hs_i_eq.symm
    rw [hs_i_coe]
    exact hconj (((a : GL (Fin (d i)) (D i)) :
      Matrix (Fin (d i)) (Fin (d i)) (D i)))
  rw [hψa', hψa, hsl_eq,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut_proj,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
  rfl

end CFSG.StandardType
