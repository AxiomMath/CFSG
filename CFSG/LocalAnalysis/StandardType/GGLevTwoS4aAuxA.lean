module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl

public section

namespace CFSG.StandardType.LevTwo

open CFSG CFSG.Assembly CFSG.LieType.RootSystem
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem levTwoS4a_data (T : LevTwoType) (hT : T.Valid) :
    GGIntCartan T.coxeter T.pair ∧
      (∀ i j, i ≠ j → T.pair i j = 0 ∨ T.pair i j = -1 ∨ T.pair i j = -2) ∧
      SecFiveRootRefl.CartanTree T.pair := by
  cases T with
  | A n =>
      exact ⟨ggIntCartan_A n, SecFiveRootRefl.entries_A n, SecFiveRootRefl.cartanTree_A n hT⟩
  | B n =>
      have hT2 : 2 ≤ n := hT
      exact ⟨ggIntCartan_B n, SecFiveRootRefl.entries_B n,
        SecFiveRootRefl.cartanTree_B n (by omega)⟩
  | D n =>
      have hT4 : 4 ≤ n := hT
      exact ⟨ggIntCartan_D n, SecFiveRootRefl.entries_D n,
        SecFiveRootRefl.cartanTree_D n hT4⟩
  | E6 =>
      exact ⟨ggIntCartan_E₆, SecFiveRootRefl.entries_E 6,
        SecFiveRootRefl.cartanTree_E 6 (by norm_num)⟩
  | E7 =>
      exact ⟨ggIntCartan_E₇, SecFiveRootRefl.entries_E 7,
        SecFiveRootRefl.cartanTree_E 7 (by norm_num)⟩
  | E8 =>
      exact ⟨ggIntCartan_E₈, SecFiveRootRefl.entries_E 8,
        SecFiveRootRefl.cartanTree_E 8 (by norm_num)⟩
  | F4 =>
      exact ⟨ggIntCartan_F₄, SecFiveRootRefl.entries_F₄, SecFiveRootRefl.cartanTree_F₄⟩

theorem levTwoS4a_ggIntCartan_transpose {Γ : Type*} {M : CoxeterMatrix Γ}
    {C : Matrix Γ Γ ℤ} (hC : GGIntCartan M C) : GGIntCartan M Cᵀ := by
  refine ⟨fun i => by simpa [Matrix.transpose_apply] using hC.1 i, fun i j hij => ?_⟩
  rcases hC.2 i j hij with ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, h12, h1, h2⟩ |
    ⟨hm, h12, h1, h2⟩
  · exact Or.inl ⟨hm, by simpa [Matrix.transpose_apply] using h2,
      by simpa [Matrix.transpose_apply] using h1⟩
  · exact Or.inr (Or.inl ⟨hm, by simpa [Matrix.transpose_apply] using h2,
      by simpa [Matrix.transpose_apply] using h1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hm, by simpa [Matrix.transpose_apply, mul_comm] using h12,
      by simpa [Matrix.transpose_apply] using h2, by simpa [Matrix.transpose_apply] using h1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hm, by simpa [Matrix.transpose_apply, mul_comm] using h12,
      by simpa [Matrix.transpose_apply] using h2, by simpa [Matrix.transpose_apply] using h1⟩))

theorem levTwoS4a_cast_simple {B : Type} [Fintype B] {M M' : CoxeterMatrix B} (h : M = M')
    (i : B) : (MulEquiv.cast h) (M.simple i) = M'.simple i := by
  cases h
  rfl

theorem levTwoS4a_cast_symm_simple {B : Type} [Fintype B] {M M' : CoxeterMatrix B}
    (h : M = M') (i : B) : (MulEquiv.cast h).symm (M'.simple i) = M.simple i := by
  cases h
  rfl

theorem levTwoS4a_isReflection_conj {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    (u φ : MulAut ↥Bs) :
    GGIsReflection p (u * φ * u⁻¹) ↔ GGIsReflection p φ := by
  have hpow : (u * φ * u⁻¹) ^ 2 = 1 ↔ φ ^ 2 = 1 := by
    have hconj : (u * φ * u⁻¹) ^ 2 = u * φ ^ 2 * u⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [hconj]
    constructor
    · intro h
      have := congrArg (fun z => u⁻¹ * z * u) h
      simpa [mul_assoc] using this
    · intro h
      rw [h]
      group
  have hcard : Nat.card {b : ↥Bs // (u * φ * u⁻¹) b = b} =
      Nat.card {b : ↥Bs // φ b = b} := by
    refine Nat.card_congr ?_
    refine Equiv.subtypeEquiv (u⁻¹ : ↥Bs ≃ ↥Bs) ?_
    intro b
    constructor
    · intro hb
      have hb' := congrArg (fun z => u⁻¹ z) hb
      simpa [MulAut.mul_apply, mul_assoc] using hb'
    · intro hb
      have hb' := congrArg (fun z => u z) hb
      simpa [MulAut.mul_apply, mul_assoc] using hb'
  rw [GGIsReflection, GGIsReflection, hpow, hcard]

@[expose] noncomputable def levTwoS4a_ell {ι : Type} [Fintype ι] {p : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (α : ι → Module.Dual (ZMod p) V) (v : ι → ℤ) :
    Module.Dual (ZMod p) V :=
  ∑ j, ((v j : ℤ) : ZMod p) • α j

theorem levTwoS4a_toLinearMap_mul {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f g : M ≃ₗ[R] M) : (f * g).toLinearMap = f.toLinearMap.comp g.toLinearMap := by
  ext x
  simp

theorem levTwoS4a_ell_reflection {ι : Type} [Fintype ι] [DecidableEq ι] {p : ℕ}
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {A C : Matrix ι ι ℤ} (hAC : Cᵀ = A)
    {h : ι → V} {α : ι → Module.Dual (ZMod p) V} (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p)) (i : ι) (v : ι → ℤ) :
    levTwoS4a_ell α (reflection A i v) =
      (levTwoS4a_ell α v).comp (Module.reflection (hα i)).toLinearMap := by
  subst hAC
  ext u
  rw [reflection_apply]
  have hL : ∀ w : ι → ℤ, levTwoS4a_ell α w u = ∑ j, ((w j : ℤ) : ZMod p) * α j u := by
    intro w
    simp only [levTwoS4a_ell, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hH : levTwoS4a_ell α v (h i) = ((∑ j, Cᵀ i j * v j : ℤ) : ZMod p) := by
    simp only [levTwoS4a_ell, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hP,
      Matrix.transpose_apply]
    push_cast
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.reflection_apply, map_sub, map_smul,
    smul_eq_mul, hH, hL, hL]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul, sub_mul,
    Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, Int.cast_one, mul_one]
    ring
  · intro b _ hb; simp [hb]
  · simp

theorem levTwoS4a_ell_weylAction {ι : Type} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {A : Matrix ι ι ℤ} (hA : TauCeti.IsFiniteType A)
    {C : Matrix ι ι ℤ} (hAC : Cᵀ = A)
    {h : ι → V} {α : ι → Module.Dual (ZMod p) V}
    (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p))
    (ρ : Wg hA →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ i, ρ (sg hA i) = Module.reflection (hα i))
    (w : Wg hA) (v : ι → ℤ) :
    levTwoS4a_ell α (weylAction hA w v) =
      (levTwoS4a_ell α v).comp ((ρ w)⁻¹).toLinearMap := by
  have hrefl_inv : ∀ i, (Module.reflection (hα i))⁻¹ = Module.reflection (hα i) :=
    fun i => Module.reflection_inv (hα i)
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left generalizing v with
  | one => simp [levTwoS4a_ell]
  | mul_simple_left w i ih =>
      rw [weylAction_mul_apply, weylAction_simple,
        levTwoS4a_ell_reflection hAC hα hP, ih,
        map_mul, hρ i, mul_inv_rev, levTwoS4a_toLinearMap_mul, LinearMap.comp_assoc,
        hrefl_inv i]

theorem matrix_rank_add_finrank_le_of_le_ker {K : Type*} [Field K] {m n : Type*} [Fintype n]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : Matrix m n K) (Φ : (n → K) →ₗ[K] V) (β : V →ₗ[K] (m → K))
    (hA : A.mulVecLin = β.comp Φ) {T : Submodule K V} (hT : T ≤ LinearMap.ker β) :
    A.rank + Module.finrank K T ≤ Module.finrank K V := by
  have hle : A.rank ≤ Module.finrank K (LinearMap.range β) := by
    have hrank : A.rank = Module.finrank K (LinearMap.range A.mulVecLin) := rfl
    rw [hrank, hA, LinearMap.range_comp]
    exact Submodule.finrank_mono (LinearMap.map_le_range (f := β))
  have hTle : Module.finrank K T ≤ Module.finrank K (LinearMap.ker β) :=
    Submodule.finrank_mono hT
  have hrn := LinearMap.finrank_range_add_finrank_ker β
  omega

theorem levTwoS4a_rank_core_add {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {Λ : Type} [Fintype Λ] {C : Matrix Λ Λ ℤ}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p))
    {T : Submodule (ZMod p) V} (hT : ∀ i, ∀ v ∈ T, α i v = 0) :
    Matrix.rank (C.map (Int.castRingHom (ZMod p))) + Module.finrank (ZMod p) T ≤
      Module.finrank (ZMod p) V := by
  classical
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  let Amat : Matrix Λ Λ (ZMod p) := C.map (Int.castRingHom (ZMod p))
  let Φ : (Λ → ZMod p) →ₗ[ZMod p] V :=
    { toFun := fun u => ∑ j, u j • h j
      map_add' := by intro u v; simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by intro a u; simp [Finset.smul_sum, smul_smul] }
  let α' : V →ₗ[ZMod p] (Λ → ZMod p) :=
    { toFun := fun v i => α i v
      map_add' := by intro v w; ext i; simp
      map_smul' := by intro a v; ext i; simp }
  have hcomp : Amat.mulVecLin = α'.comp Φ := by
    refine LinearMap.ext fun u => ?_
    refine funext fun i => ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply, Matrix.row, LinearMap.comp_apply]
    show (∑ j, Amat i j * u j) = α i (∑ j, u j • h j)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, hP]
    show Amat i j * u j = u j * (C i j : ZMod p)
    rw [show Amat i j = (C i j : ZMod p) from rfl]
    ring
  have hT' : T ≤ LinearMap.ker α' := by
    intro v hv
    ext i
    exact hT i v hv
  simpa only [Amat] using matrix_rank_add_finrank_le_of_le_ker Amat Φ α' hcomp hT'

theorem levTwoS4a_rank_core_add_one {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {Λ : Type} [Fintype Λ] {C : Matrix Λ Λ ℤ}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p))
    {x : V} (hx : x ≠ 0) (hxα : ∀ i, α i x = 0) :
    Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 ≤ Module.finrank (ZMod p) V := by
  have h := levTwoS4a_rank_core_add (p := p) (V := V) (C := C) (h := h) (α := α) hP
    (T := Submodule.span (ZMod p) ({x} : Set V)) (by
      intro i v hv
      rw [Submodule.mem_span_singleton] at hv
      obtain ⟨c, rfl⟩ := hv
      rw [map_smul, hxα i, smul_zero])
  rwa [finrank_span_singleton hx] at h

theorem levTwoS4a_rank_core {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    {h : Fin n → V} {α : Fin n → Module.Dual (ZMod p) V}
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p)) :
    Matrix.rank (C.map (Int.castRingHom (ZMod p))) ≤ Module.finrank (ZMod p) V := by
  simpa using levTwoS4a_rank_core_add (p := p) (V := V) (C := C) (h := h) (α := α) hP
    (T := ⊥) (by simp)

theorem levTwoS4a_exactThree_rank_squeeze_of_axis_bound {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {α : Λ → Module.Dual (ZMod p) V}
    (haxis : Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 ≤
      Module.finrank (ZMod p) V)
    (S : Finset Λ) (hS : S.card = 3)
    (hnull : Fintype.card Λ ≤ Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1)
    (hker : Module.finrank (ZMod p)
      (LinearMap.ker (LinearMap.pi fun i : {i : Λ // i ∉ S} => α i.1)) ≤ 3) :
    Module.finrank (ZMod p) V = Fintype.card Λ ∧
      Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 = Fintype.card Λ ∧
      Module.finrank (ZMod p)
        (LinearMap.ker (LinearMap.pi fun i : {i : Λ // i ∉ S} => α i.1)) = 3 := by
  classical
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  let β : V →ₗ[ZMod p] ({i : Λ // i ∉ S} → ZMod p) :=
    LinearMap.pi fun i => α i.1
  have hcard : Fintype.card {i : Λ // i ∉ S} + 3 = Fintype.card Λ := by
    have heq : Fintype.card {i : Λ // i ∉ S} = Sᶜ.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext i
      simp
    rw [heq, ← hS]
    exact Finset.card_compl_add_card S
  have hrange : Module.finrank (ZMod p) (LinearMap.range β) ≤
      Fintype.card {i : Λ // i ∉ S} := by
    have hcod : Module.finrank (ZMod p) ({i : Λ // i ∉ S} → ZMod p) =
        Fintype.card {i : Λ // i ∉ S} := Module.finrank_fintype_fun_eq_card (ZMod p)
    exact (Submodule.finrank_le (LinearMap.range β)).trans_eq hcod
  have hrn := LinearMap.finrank_range_add_finrank_ker β
  change Module.finrank (ZMod p) (LinearMap.ker β) ≤ 3 at hker
  change Module.finrank (ZMod p) V = Fintype.card Λ ∧
    Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 = Fintype.card Λ ∧
    Module.finrank (ZMod p) (LinearMap.ker β) = 3
  omega

end CFSG.StandardType.LevTwo
