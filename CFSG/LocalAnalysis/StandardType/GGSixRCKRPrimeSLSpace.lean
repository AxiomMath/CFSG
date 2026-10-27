module

public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGL
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped Matrix

private lemma rckRPsl_toLin_single {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {n : ℕ} (b : Module.Basis (Fin n) K W) {i j : Fin n} (t : K) :
    Matrix.toLin b b (Matrix.single i j t) = (b.coord j).smulRight (t • b i) := by
  have hmat : Matrix.single i j t = Matrix.vecMulVec (b.repr (t • b i)) (b.coord j ∘ b) := by
    ext i' l
    by_cases hi : i = i' <;> by_cases hj : j = l <;>
      simp_all [Matrix.single_apply, Matrix.vecMulVec_apply, Module.Basis.coord_apply,
        Module.Basis.repr_self, map_smul, Finsupp.smul_apply, Finsupp.single_apply]
  rw [← Matrix.toLin_toMatrix b b ((b.coord j).smulRight (t • b i)),
    LinearMap.toMatrix_smulRight, hmat]

private lemma rckRPsl_toLin'_coe {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {n : ℕ} (b : Module.Basis (Fin n) K W)
    (M : Matrix.GeneralLinearGroup (Fin n) K) :
    ((Matrix.GeneralLinearGroup.toLin' b M).toLinearEquiv : W →ₗ[K] W) =
      Matrix.toLin b b (M : Matrix (Fin n) (Fin n) K) := by
  refine b.ext fun i => ?_
  change (Matrix.GeneralLinearGroup.toLin' b M).toLinearEquiv (b i) =
    Matrix.toLin b b (M : Matrix (Fin n) (Fin n) K) (b i)
  rw [Matrix.GeneralLinearGroup.toLin'_apply, Matrix.toLin_self]
  simp [Fintype.linearCombination_apply, Module.Basis.repr_self,
    Finsupp.single_eq_pi_single, Matrix.mulVec_single_one]

private noncomputable def rckRPsl_rho {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {q k : ℕ} (tau : GaloisField 2 q ≃+* K)
    (b : Module.Basis (Fin (k + 1)) K W) :
    Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 q) →* (W ≃ₗ[K] W) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).toMonoidHom.comp <|
    (Matrix.GeneralLinearGroup.toLin' b).toMonoidHom.comp <|
      Matrix.SpecialLinearGroup.toGL.comp <|
        Matrix.SpecialLinearGroup.map tau.toRingHom

private lemma rckRPsl_rho_toLin {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {q k : ℕ} (tau : GaloisField 2 q ≃+* K)
    (b : Module.Basis (Fin (k + 1)) K W)
    (y : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 q)) :
    ((rckRPsl_rho tau b y : W →ₗ[K] W)) =
      Matrix.toLin b b
        ((Matrix.SpecialLinearGroup.coeMonoidHom y).map tau.toRingHom) := by
  unfold rckRPsl_rho
  simp only [MonoidHom.comp_apply]
  rw [show (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).toMonoidHom
      ((Matrix.GeneralLinearGroup.toLin' b).toMonoidHom
        (Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map tau.toRingHom y))) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K W)
        ((Matrix.GeneralLinearGroup.toLin' b)
          (Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.map tau.toRingHom y))) from rfl]
  rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  change ((Matrix.GeneralLinearGroup.toLin' b (Matrix.SpecialLinearGroup.toGL
    (Matrix.SpecialLinearGroup.map tau.toRingHom y))).toLinearEquiv : W →ₗ[K] W) = _
  rw [rckRPsl_toLin'_coe]
  rw [Matrix.SpecialLinearGroup.coeMonoidHom_apply]
  rfl

private lemma rckRPsl_map_transvection {R S : Type} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) {i j : Fin n} (hij : i ≠ j) (c : R) :
    ((Matrix.SpecialLinearGroup.transvection hij c : Matrix (Fin n) (Fin n) R)).map f =
      Matrix.transvection i j (f c) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  by_cases h : i = a ∧ j = b <;>
    simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, h, map_one, map_zero]

private lemma rckRPsl_rho_transvection_sub {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {q k : ℕ} (tau : GaloisField 2 q ≃+* K)
    (b : Module.Basis (Fin (k + 1)) K W) {i j : Fin (k + 1)} (hij : i ≠ j)
    (c : GaloisField 2 q) :
    ((rckRPsl_rho tau b (Matrix.SpecialLinearGroup.transvection hij c) : W →ₗ[K] W) -
        LinearMap.id) = (b.coord j).smulRight (tau c • b i) := by
  rw [rckRPsl_rho_toLin]
  rw [Matrix.SpecialLinearGroup.coeMonoidHom_apply]
  rw [rckRPsl_map_transvection tau.toRingHom hij c]
  change Matrix.toLin b b (1 + Matrix.single i j (tau c)) - LinearMap.id = _
  rw [map_add, Matrix.toLin_one, add_sub_cancel_left]
  exact rckRPsl_toLin_single b (tau c)

private lemma rckRPsl_isMulCommutative_finrank_one {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (hdim : Module.finrank K W = 1) :
    IsMulCommutative (W ≃ₗ[K] W) := by
  refine ⟨⟨fun f g => ?_⟩⟩
  obtain ⟨c, hc⟩ := (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
    (f : W →ₗ[K] W)).exists
  obtain ⟨d, hd⟩ := (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
    (g : W →ₗ[K] W)).exists
  have hfx : ∀ y, f y = c • y := fun y => by
    have := congrArg (fun m : W →ₗ[K] W => m y) hc
    simpa using this
  have hgx : ∀ y, g y = d • y := fun y => by
    have := congrArg (fun m : W →ₗ[K] W => m y) hd
    simpa using this
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [hfx (g x), hgx x, hgx (f x), hfx x]
  rw [smul_comm]

private lemma rckRPsl_map_injective {K : Type} [Field K] {q k : ℕ}
    (tau : GaloisField 2 q ≃+* K) :
    Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.toRingHom) := by
  intro x y hxy
  have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin (k + 1)) K =>
    Matrix.SpecialLinearGroup.coeMonoidHom z) hxy
  apply Subtype.ext
  ext i j
  have h' := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) K => M i j) h
  rw [show Matrix.SpecialLinearGroup.coeMonoidHom
      (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.toRingHom x) =
      tau.toRingHom.mapMatrix (Matrix.SpecialLinearGroup.coeMonoidHom x) from rfl,
    show Matrix.SpecialLinearGroup.coeMonoidHom
      (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.toRingHom y) =
      tau.toRingHom.mapMatrix (Matrix.SpecialLinearGroup.coeMonoidHom y) from rfl] at h'
  simp only [RingHom.mapMatrix_apply] at h'
  rw [← Matrix.SpecialLinearGroup.coeMonoidHom_apply x,
    ← Matrix.SpecialLinearGroup.coeMonoidHom_apply y]
  exact tau.injective h'

private lemma rckRPsl_map_surjective {K : Type} [Field K] {q k : ℕ}
    (tau : GaloisField 2 q ≃+* K) :
    (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.toRingHom).range = ⊤ := by
  rw [MonoidHom.range_eq_top]
  intro x
  refine ⟨Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.symm.toRingHom x, ?_⟩
  apply Subtype.ext
  ext i j
  rw [← Matrix.SpecialLinearGroup.coeMonoidHom_apply
      (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.toRingHom
        (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.symm.toRingHom x)),
    ← Matrix.SpecialLinearGroup.coeMonoidHom_apply x]
  rw [show Matrix.SpecialLinearGroup.coeMonoidHom
      (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.toRingHom
        (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.symm.toRingHom x)) =
      tau.toRingHom.mapMatrix (Matrix.SpecialLinearGroup.coeMonoidHom
        (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.symm.toRingHom x)) from rfl,
    show Matrix.SpecialLinearGroup.coeMonoidHom
      (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) tau.symm.toRingHom x) =
      tau.symm.toRingHom.mapMatrix (Matrix.SpecialLinearGroup.coeMonoidHom x) from rfl]
  simp [RingHom.mapMatrix_apply]

private lemma rckRPsl_injective {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {q k : ℕ} (tau : GaloisField 2 q ≃+* K)
    (b : Module.Basis (Fin (k + 1)) K W) :
    Function.Injective (rckRPsl_rho tau b) := by
  have h1 := rckRPsl_map_injective (k := k) tau
  have h2 : Function.Injective
      (Matrix.SpecialLinearGroup.toGL (n := Fin (k + 1)) (R := K)) :=
    Matrix.SpecialLinearGroup.toGL_injective
  have h3 : Function.Injective (Matrix.GeneralLinearGroup.toLin' b) :=
    (Matrix.GeneralLinearGroup.toLin' b).injective
  have h4 : Function.Injective (LinearMap.GeneralLinearGroup.generalLinearEquiv K W) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).injective
  intro x y hxy
  exact h1 (h2 (h3 (h4 (by simpa [rckRPsl_rho] using hxy))))

private lemma rckRPsl_hcond {K : Type} [Field K] [Finite K] {q k : ℕ}
    (hK : Nat.card K = 2 ^ q) (hq : 2 ≤ q) (hk1 : 1 ≤ k) :
    3 ≤ k + 1 ∨ ∃ s : Finset K, s.card = 4 := by
  haveI : Fintype K := Fintype.ofFinite K
  rcases Nat.lt_or_ge (k + 1) 3 with h3 | h3
  · right
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq
    have h4' : 4 ≤ (Finset.univ : Finset K).card := by
      simpa [Nat.card_eq_fintype_card] using h4
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4'
    exact ⟨s, hs⟩
  · exact Or.inl h3

private lemma rckRPsl_range_eq {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W]
    [Module K W] {q k : ℕ} (tau : GaloisField 2 q ≃+* K)
    (b : Module.Basis (Fin (k + 1)) K W) (hk1 : 1 ≤ k)
    (hcond : 3 ≤ k + 1 ∨ ∃ s : Finset K, s.card = 4) :
    (rckRPsl_rho tau b).range = commutator (W ≃ₗ[K] W) := by
  have hmap := rckRPsl_map_surjective (k := k) tau
  have htoGL : (Matrix.SpecialLinearGroup.toGL (n := Fin (k + 1)) (R := K)).range =
      commutator (Matrix.GeneralLinearGroup (Fin (k + 1)) K) := by
    rw [← CFSG.Open.StatedAPI.statedSL_eq_range_toGL,
      GGNbrLSideKit.commutator_generalLinear_eq_statedSL (by omega) hcond]
  let ψ : Matrix.GeneralLinearGroup (Fin (k + 1)) K →* (W ≃ₗ[K] W) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin' b).toMonoidHom
  have hrho : rckRPsl_rho tau b = ψ.comp (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map tau.toRingHom)) := rfl
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨g, hg⟩ := (Matrix.GeneralLinearGroup.toLin' b).surjective
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm x)
    refine ⟨g, ?_⟩
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv K W)
      ((Matrix.GeneralLinearGroup.toLin' b) g) = x
    rw [hg, MulEquiv.apply_symm_apply]
  rw [hrho, MonoidHom.range_comp, MonoidHom.range_comp]
  rw [hmap, Subgroup.map_top, htoGL]
  change Subgroup.map ψ ⁅(⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin (k + 1)) K)),
      (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin (k + 1)) K))⁆ =
    ⁅(⊤ : Subgroup (W ≃ₗ[K] W)), (⊤ : Subgroup (W ≃ₗ[K] W))⁆
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ hψsurj]

private lemma rckRPsl_coord_ne_zero {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {n : ℕ} (b : Module.Basis (Fin n) K W) (j : Fin n) :
    b.coord j ≠ 0 := by
  intro h
  have h1 : b.coord j (b j) = 1 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  simpa [h] using h1

private lemma rckRPsl_span_le_ker {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {n : ℕ} (b : Module.Basis (Fin n) K W) {i j : Fin n} (hij : i ≠ j) :
    Submodule.span K {b i} ≤ LinearMap.ker (b.coord j) := by
  rw [Submodule.span_le]
  rintro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  change b i ∈ LinearMap.ker (b.coord j)
  rw [LinearMap.mem_ker, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_of_ne' hij]

private lemma rckRPsl_range_transvection {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {q k : ℕ} (tau : GaloisField 2 q ≃+* K)
    (b : Module.Basis (Fin (k + 1)) K W) {i j : Fin (k + 1)} (hij : i ≠ j)
    {c : GaloisField 2 q} (hc : c ≠ 0) :
    LinearMap.range ((rckRPsl_rho tau b
      (Matrix.SpecialLinearGroup.transvection hij c) : W →ₗ[K] W) - LinearMap.id) =
        Submodule.span K {b i} := by
  have htau : tau c ≠ 0 := by
    intro h
    exact hc (tau.injective (by simpa using h))
  rw [rckRPsl_rho_transvection_sub]
  rw [LinearMap.range_smulRight_apply]
  · rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr htau)]
  · exact rckRPsl_coord_ne_zero b j

private lemma rckRPsl_ker_transvection {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {q k : ℕ} (tau : GaloisField 2 q ≃+* K)
    (b : Module.Basis (Fin (k + 1)) K W) {i j : Fin (k + 1)} (hij : i ≠ j)
    {c : GaloisField 2 q} (hc : c ≠ 0) :
    LinearMap.ker ((rckRPsl_rho tau b
      (Matrix.SpecialLinearGroup.transvection hij c) : W →ₗ[K] W) - LinearMap.id) =
        LinearMap.ker (b.coord j) := by
  have htau : tau c ≠ 0 := by
    intro h
    exact hc (tau.injective (by simpa using h))
  rw [rckRPsl_rho_transvection_sub]
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.smulRight_apply]
  constructor
  · intro hv
    have hx : tau c • b i ≠ 0 := by
      intro h
      rcases smul_eq_zero.mp h with h' | h'
      · exact htau h'
      · exact (b.ne_zero _) h'
    rcases smul_eq_zero.mp hv with h | h
    · exact h
    · exact absurd h hx
  · intro hv
    rw [hv, zero_smul]

private lemma rckRPsl_rootGroup_involution {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {q k : ℕ} (tau : GaloisField 2 q ≃+* K)
    (b : Module.Basis (Fin (k + 1)) K W)
    {β : Fin k → ℤ} (hβ : β ∈ roots (SpecialLinear.isFiniteType_A k) ∅) :
    ∀ y ∈ (SpecialLinear.rootDatum k (GaloisField 2 q)).rootGroup β, y * y = 1 := by
  let i := (SpecialLinear.idx k β).1
  let j := (SpecialLinear.idx k β).2
  have hij : i ≠ j := (SpecialLinear.idx_spec k hβ).1
  have hroot : (SpecialLinear.rootDatum k (GaloisField 2 q)).rootGroup β =
      SpecialLinear.rootSubgroup k (GaloisField 2 q) hij :=
    SpecialLinear.rootGroup_eq_idx k (GaloisField 2 q) hβ
  intro y hy
  rw [hroot] at hy
  obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij y).mp hy
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  haveI : CharP (GaloisField 2 q) 2 := inferInstance
  have h : (Matrix.transvection i j c) * (Matrix.transvection i j c) = 1 := by
    rw [Matrix.transvection_mul_transvection_same i j hij, CharTwo.add_self_eq_zero,
      Matrix.transvection_zero]
  simpa [Matrix.transvection] using h

private lemma rckRPsl_rootGroup_flag {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {q k : ℕ} (tau : GaloisField 2 q ≃+* K)
    (b : Module.Basis (Fin (k + 1)) K W)
    {β : Fin k → ℤ} (hβ : β ∈ roots (SpecialLinear.isFiniteType_A k) ∅) :
    ∃ U₁ U₂ : Submodule K W, U₁ ≤ U₂ ∧
      ∀ y ∈ (SpecialLinear.rootDatum k (GaloisField 2 q)).rootGroup β, y ≠ 1 →
        LinearMap.range ((rckRPsl_rho tau b y : W →ₗ[K] W) - LinearMap.id) = U₁ ∧
        LinearMap.ker ((rckRPsl_rho tau b y : W →ₗ[K] W) - LinearMap.id) = U₂ := by
  let i := (SpecialLinear.idx k β).1
  let j := (SpecialLinear.idx k β).2
  have hij : i ≠ j := (SpecialLinear.idx_spec k hβ).1
  have hroot : (SpecialLinear.rootDatum k (GaloisField 2 q)).rootGroup β =
      SpecialLinear.rootSubgroup k (GaloisField 2 q) hij :=
    SpecialLinear.rootGroup_eq_idx k (GaloisField 2 q) hβ
  refine ⟨Submodule.span K {b i}, LinearMap.ker (b.coord j),
    rckRPsl_span_le_ker b hij, ?_⟩
  intro y hy hyne
  rw [hroot] at hy
  obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij y).mp hy
  have hc : c ≠ 0 := by
    intro hc0
    apply hyne
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.transvection_coe, hc0,
      Matrix.single_zero, add_zero, Matrix.SpecialLinearGroup.coe_one]
  exact ⟨rckRPsl_range_transvection tau b hij hc,
    rckRPsl_ker_transvection tau b hij hc⟩

theorem exists_slModel_linearEquiv {K : Type} [Field K] [Finite K] {q k : ℕ}
    (hK : Nat.card K = 2 ^ q) (hq : 2 ≤ q) {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (hW : Module.finrank K W = k + 1) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 q) →* (W ≃ₗ[K] W),
      Function.Injective ρ ∧ ρ.range = commutator (W ≃ₗ[K] W) ∧
      ∀ β ∈ (SpecialLinear.rootDatum k (GaloisField 2 q)).roots,
        (∀ y ∈ (SpecialLinear.rootDatum k (GaloisField 2 q)).rootGroup β, y * y = 1) ∧
        ∃ U₁ U₂ : Submodule K W, U₁ ≤ U₂ ∧
          ∀ y ∈ (SpecialLinear.rootDatum k (GaloisField 2 q)).rootGroup β, y ≠ 1 →
            LinearMap.range ((ρ y : W →ₗ[K] W) - LinearMap.id) = U₁ ∧
            LinearMap.ker ((ρ y : W →ₗ[K] W) - LinearMap.id) = U₂ := by
  classical
  by_cases hk : k = 0
  · subst hk
    have hdim : Module.finrank K W = 1 := by simpa using hW
    haveI : IsMulCommutative (W ≃ₗ[K] W) :=
      rckRPsl_isMulCommutative_finrank_one hdim
    haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b => by ext; omega⟩
    haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin (0 + 1)) (GaloisField 2 q)) :=
      Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
    refine ⟨1, ?_, ?_, ?_⟩
    · intro x y _
      exact Subsingleton.elim x y
    · rw [MonoidHom.range_one]
      change ⊥ = ⁅(⊤ : Subgroup (W ≃ₗ[K] W)), ⊤⁆
      rw [eq_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      change ⊤ ≤ Subgroup.centralizer (Set.univ : Set (W ≃ₗ[K] W))
      rw [Subgroup.centralizer_univ, Subgroup.center_eq_top]
    · intro β hβ
      change β ∈ roots (SpecialLinear.isFiniteType_A 0) ∅ at hβ
      rw [SpecialLinear.roots_eq] at hβ
      obtain ⟨i, j, hij, -⟩ := hβ
      exact absurd (Subsingleton.elim i j) hij
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
    have hq0 : q ≠ 0 := by omega
    have hcard : Nat.card (GaloisField 2 q) = Nat.card K := by
      rw [GaloisField.card 2 q hq0, hK]
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fintype (GaloisField 2 q) := Fintype.ofFinite _
    have hcard' : Fintype.card (GaloisField 2 q) = Fintype.card K := by
      rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    let tau : GaloisField 2 q ≃+* K := FiniteField.ringEquivOfCardEq hcard'
    let b : Module.Basis (Fin (k + 1)) K W := Module.finBasisOfFinrankEq K W hW
    refine ⟨rckRPsl_rho tau b, rckRPsl_injective tau b,
      rckRPsl_range_eq tau b hk1 (rckRPsl_hcond hK hq hk1), ?_⟩
    intro β hβ
    change β ∈ roots (SpecialLinear.isFiniteType_A k) ∅ at hβ
    exact ⟨rckRPsl_rootGroup_involution tau b hβ, rckRPsl_rootGroup_flag tau b hβ⟩

end CFSG.StandardType.RCKRP
