module
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaNormElements
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCZ1
public import CFSG.Mathlib.LinearAlgebra.F3NormOneOrthogonal
import Lean.Elab.Tactic.Omega.Frontend
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Group

open Subgroup Matrix CFSG.StandardType CFSG.StandardType.FrameRoute.FS81

public noncomputable section
namespace CFSG.StandardType.FrameRoute.FS81
private theorem norm_one_iff_weight (v : Coords 8) :
    v ⬝ᵥ v = 1 ↔ wt v = 1 ∨ wt v = 4 ∨ wt v = 7 := by
  have hw : v ⬝ᵥ v = (wt v : ZMod 3) := ggQ2x_dot_self_eq_wt v
  have hle : wt v ≤ 8 := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin 8)) (fun i => v i ≠ 0)
    simpa only [wt, Finset.card_univ, Fintype.card_fin] using h
  rw [hw]
  constructor
  · intro h
    have hval := congrArg ZMod.val h
    have h1 : ZMod.val (1 : ZMod 3) = 1 := by decide +kernel
    rw [h1] at hval
    have hmod : wt v % 3 = 1 := by simpa using hval
    omega
  · rintro (h | h | h) <;> rw [h] <;> decide +kernel
private theorem isConjLine_map_conj_iff {G : Type} [Group G] (a x : G) (Z : Subgroup G) :
    IsConjLine a (Z.map (MulAut.conj x).toMonoidHom) ↔ IsConjLine a Z := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨x⁻¹ * t, ?_⟩
    apply Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
    rw [MonoidHom.map_zpowers]
    change zpowers (x * ((x⁻¹ * t) * a * (x⁻¹ * t)⁻¹) * x⁻¹) =
      Z.map (MulAut.conj x).toMonoidHom
    have heq : x * ((x⁻¹ * t) * a * (x⁻¹ * t)⁻¹) * x⁻¹ = t * a * t⁻¹ := by group
    rw [heq]
    exact ht
  · rintro ⟨t, ht⟩
    refine ⟨x * t, ?_⟩
    rw [← ht, MonoidHom.map_zpowers]
    change zpowers ((x * t) * a * (x * t)⁻¹) = zpowers (x * (t * a * t⁻¹) * x⁻¹)
    congr 1
    group
theorem transpose_mul_self_of_recOutTwD7 {G : Type} [Group G] [Finite G]
    (B : Basis3 G 8) (b₀ : G) (hrec : RecOutTwD7 B b₀)
    (x : G) (M : Matrix (Fin 8) (Fin 8) (ZMod 3)) (hA : B.Acts x M) : Mᵀ * M = 1 := by
  have hinj : Function.Injective M.mulVec := by
    intro v w h
    apply B.vec_injective
    apply (MulAut.conj x).injective
    change x * B.vec v * x⁻¹ = x * B.vec w * x⁻¹
    rw [B.acts_vec hA v, B.acts_vec hA w, h]
  have hline : ∀ v, (B.line v).map (MulAut.conj x).toMonoidHom = B.line (M *ᵥ v) := by
    intro v
    rw [Basis3.line, MonoidHom.map_zpowers]
    change zpowers (x * B.vec v * x⁻¹) = zpowers (B.vec (M *ᵥ v))
    rw [B.acts_vec hA v]
  apply Matrix.transpose_mul_self_of_dot_self_one_iff
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · have hMv : M *ᵥ v ≠ 0 := by
      intro h
      apply hv
      apply hinj
      simpa using h
    rw [norm_one_iff_weight, norm_one_iff_weight, ← hrec.2.1 _ hMv, ← hrec.2.1 _ hv,
      ← hline v]
    exact isConjLine_map_conj_iff b₀ x (B.line v)
private theorem swap_matrix_eq_one_sub {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    spMat (Equiv.swap a b) (fun _ => 1) =
      (1 : Matrix (Fin n) (Fin n) (ZMod 3)) -
        vecMulVec (Pi.single a 1 - Pi.single b 1) (Pi.single a 1 - Pi.single b 1) := by
  ext i j
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp_all [spMat, vecMulVec, Pi.single_apply, Equiv.swap_apply_def, Matrix.one_apply]
private theorem conjugate_outer_reflection {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 3)) (r s : Fin n → ZMod 3) (c : ZMod 3)
    (hMM : M * Mᵀ = 1) (hr : M *ᵥ r = c • s) (hc : c * c = 1) :
    M * (1 - vecMulVec r r) * Mᵀ = 1 - vecMulVec s s := by
  calc
    _ = M * Mᵀ - (M * vecMulVec r r) * Mᵀ := by rw [mul_sub, mul_one, sub_mul]
    _ = 1 - vecMulVec (M *ᵥ r) (r ᵥ* Mᵀ) := by
      rw [hMM, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    _ = 1 - vecMulVec (M *ᵥ r) (M *ᵥ r) := by rw [Matrix.vecMul_transpose]
    _ = 1 - vecMulVec s s := by
      rw [hr]
      congr 1
      ext i j
      change (c * s i) * (c * s j) = s i * s j
      calc
        _ = (c * c) * (s i * s j) := by ring
        _ = _ := by rw [hc, one_mul]
private theorem exists_involutive_perm_action_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (σ : Equiv.Perm (Fin 8)) (hσ0 : σ 0 = 0) (hσ2 : Function.Involutive σ) :
    ∃ u ∈ K, u ∈ normalizer (E : Set G) ∧ u ^ 2 = 1 ∧
      B.Acts u (spMat σ (fun _ => 1)) := by
  have hmat : spMat σ (fun _ => 1) ∈ evenFix0 7 :=
    ⟨σ, (fun _ => 1), (fun _ => Or.inl rfl), ⟨hσ0, rfl, by simp⟩, rfl⟩
  have hr : spMat σ (fun _ => 1) ∈ B.realized K :=
    (realized_eq_evenFix0_of_std_twD7 hstd B hB hrec).symm ▸ hmat
  obtain ⟨u, huK, huA⟩ := hr
  have huE : u ∈ normalizer (E : Set G) := hB.1 ▸ B.mem_normalizer_of_acts huA
  have huPoint : ∀ j : Fin 8, u * B.b j * u⁻¹ = B.b (σ j) := by
    intro j
    have hcol : (fun i => spMat σ (fun _ => 1) i j) = Pi.single (σ j) 1 := by
      ext i
      simp [spMat, Pi.single_apply]
    rw [huA j, hcol, B.vec_single]
  have hu2point : ∀ j : Fin 8, u ^ 2 * B.b j * (u ^ 2)⁻¹ = B.b j := by
    intro j
    calc
      _ = u * (u * B.b j * u⁻¹) * u⁻¹ := by
        rw [pow_two]
        group
      _ = u * B.b (σ j) * u⁻¹ := by rw [huPoint j]
      _ = B.b (σ (σ j)) := huPoint (σ j)
      _ = B.b j := by rw [hσ2 j]
  have hspan : B.span ≤ centralizer ({u ^ 2} : Set G) := by
    change Subgroup.closure (Set.range B.b) ≤ _
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨j, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hcomm : u ^ 2 * B.b j = B.b j * u ^ 2 := by
      calc
        _ = (u ^ 2 * B.b j * (u ^ 2)⁻¹) * u ^ 2 := by group
        _ = B.b j * u ^ 2 := by rw [hu2point j]
    exact hcomm.symm
  have hu2CK : u ^ 2 ∈ centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K := by
    refine ⟨mem_centralizer_iff.mpr ?_, pow_mem huK 2⟩
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hspan (hB.1.symm ▸ hx.1))
  obtain ⟨-, -, -, hAmax, -, hAcen⟩ := hstd.2.2
  rw [hAcen] at hu2CK
  have hu2cube : (u ^ 2) ^ 3 = 1 := hAmax.2.1.2 (u ^ 2) hu2CK
  have hu3square : (u ^ 3) ^ 2 = 1 := by
    calc
      _ = u ^ (3 * 2) := (pow_mul u 3 2).symm
      _ = u ^ (2 * 3) := rfl
      _ = (u ^ 2) ^ 3 := pow_mul u 2 3
      _ = 1 := hu2cube
  have hu3point : ∀ j : Fin 8, u ^ 3 * B.b j * (u ^ 3)⁻¹ = B.b (σ j) := by
    intro j
    calc
      _ = u ^ 2 * (u * B.b j * u⁻¹) * (u ^ 2)⁻¹ := by group
      _ = u ^ 2 * B.b (σ j) * (u ^ 2)⁻¹ := by rw [huPoint j]
      _ = B.b (σ j) := hu2point (σ j)
  refine ⟨u ^ 3, pow_mem huK 3, pow_mem huE 3, hu3square, ?_⟩
  intro j
  have hcol : (fun i => spMat σ (fun _ => 1) i j) = Pi.single (σ j) 1 := by
    ext i
    simp [spMat, Pi.single_apply]
  rw [hu3point j, hcol, B.vec_single]

theorem exists_root_reflection_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) (v : Coords 8)
    (hroot : wt v = 2 ∨ (wt v = 8 ∧ ∏ i : Fin 8, v i = -1)) :
    ∃ g ∈ normalizer (E : Set G), orderOf g = 2 ∧ B.Acts g (1 - vecMulVec v v) := by
  classical
  let r : Coords 8 := Pi.single 1 1 - Pi.single 2 1
  have hwr : wt r = 2 := ggQ2x_wt_sub_single 1 2 (by decide)
  have hr : r ≠ 0 := by
    intro hz
    have hh := hwr
    rw [hz] at hh
    simp [wt] at hh
  have hv : v ≠ 0 := by
    intro hz
    rcases hroot with hh | ⟨hh, -⟩ <;> rw [hz] at hh <;> simp [wt] at hh
  obtain ⟨u, -, huE, hu2, huA⟩ :=
    exists_involutive_perm_action_of_std_twD7 hstd B hB hrec
      (Equiv.swap 1 2) (by decide) (fun j => by simp)
  have hrr := (hrec.2.2 r hr).mpr (Or.inl hwr)
  have hvv := (hrec.2.2 v hv).mpr hroot
  rw [hB.1] at hrr hvv
  obtain ⟨gr, hgr, heqr⟩ := hrr
  obtain ⟨gv, hgv, heqv⟩ := hvv
  let x := gv * gr⁻¹
  have hxE : x ∈ normalizer (E : Set G) := mul_mem hgv (inv_mem hgr)
  have hxline : (B.line r).map (MulAut.conj x).toMonoidHom = B.line v := by
    rw [← heqr, MonoidHom.map_zpowers]
    change zpowers (x * (gr * (b₀ * B.b 1) * gr⁻¹) * x⁻¹) = B.line v
    have hprod : x * (gr * (b₀ * B.b 1) * gr⁻¹) * x⁻¹ = gv * (b₀ * B.b 1) * gv⁻¹ := by
      dsimp only [x]
      group
    rw [hprod]
    exact heqv
  have hxN : x ∈ normalizer (B.span : Set G) := hB.1.symm ▸ hxE
  let zN : normalizer (B.span : Set G) := ⟨x, hxN⟩
  let φ : MulAut B.span := B.span.normalizerMonoidHom zN
  let φ' : MulAut B.span := B.span.normalizerMonoidHom zN⁻¹
  let M : Matrix (Fin 8) (Fin 8) (ZMod 3) := B.matOf φ
  let N : Matrix (Fin 8) (Fin 8) (ZMod 3) := B.matOf φ'
  have hφ' : φ' = φ⁻¹ := B.span.normalizerMonoidHom.map_inv zN
  have hxA : B.Acts x M :=
    B.acts_matOf (fun y => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _)
  have hxA' : B.Acts x⁻¹ N :=
    B.acts_matOf (fun y => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _)
  have hMN : M * N = 1 := by
    dsimp only [M, N]
    rw [← B.matOf_mul, hφ', mul_inv_cancel, B.matOf_one]
  have hNM : N * M = 1 := by
    dsimp only [M, N]
    rw [← B.matOf_mul, hφ', inv_mul_cancel, B.matOf_one]
  have hMtM : Mᵀ * M = 1 := transpose_mul_self_of_recOutTwD7 B b₀ hrec x M hxA
  have hNt : Mᵀ = N := by
    calc
      _ = Mᵀ * (M * N) := by rw [hMN, mul_one]
      _ = (Mᵀ * M) * N := (Matrix.mul_assoc _ _ _).symm
      _ = N := by rw [hMtM, one_mul]
  have hMMt : M * Mᵀ = 1 := by rw [hNt, hMN]
  have hMr : M *ᵥ r ≠ 0 := by
    intro h
    apply hr
    have hh : N *ᵥ (M *ᵥ r) = r := by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at hh
    exact hh.symm
  have hmem : B.vec (M *ᵥ r) ∈ zpowers (B.vec v) := by
    have hh : x * B.vec r * x⁻¹ ∈ (B.line r).map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers _)
    rw [B.acts_vec hxA r, hxline] at hh
    exact hh
  have hrootM : M *ᵥ r = v ∨ M *ᵥ r = -v := B.eq_or_eq_neg_of_vec_mem_zpowers hMr hmem
  have hconj : M * spMat (Equiv.swap 1 2) (fun _ => 1) * Mᵀ = 1 - vecMulVec v v := by
    rw [swap_matrix_eq_one_sub 1 2 (by decide)]
    change M * (1 - vecMulVec r r) * Mᵀ = 1 - vecMulVec v v
    rcases hrootM with h | h
    · exact conjugate_outer_reflection M r v 1 hMMt (by simpa using h) (by simp)
    · exact conjugate_outer_reflection M r v (-1) hMMt (by simpa using h) (by simp)
  let g := x * u * x⁻¹
  have hgE : g ∈ normalizer (E : Set G) := mul_mem (mul_mem hxE huE) (inv_mem hxE)
  have hgA : B.Acts g (1 - vecMulVec v v) := by
    have hh := B.acts_mul (B.acts_mul hxA huA) hxA'
    rw [← hNt, hconj] at hh
    exact hh
  have hg2 : g ^ 2 = 1 := by
    calc
      _ = x * (u ^ 2) * x⁻¹ := by dsimp only [g]; simp only [pow_two]; group
      _ = 1 := by rw [hu2]; group
  have hcoord : ∃ i, v i ≠ 0 := by
    by_contra hn
    apply hv
    funext i
    change v i = 0
    by_contra hi
    exact hn ⟨i, hi⟩
  have hgne : g ≠ 1 := by
    intro hz
    obtain ⟨i, hi⟩ := hcoord
    have hcol : (Pi.single i 1 : Coords 8) = fun j => (1 - vecMulVec v v) j i := by
      apply B.vec_injective
      rw [B.vec_single]
      simpa only [hz, one_mul, inv_one, mul_one] using hgA i
    have hii := congrFun hcol i
    have hh : (1 : ZMod 3) = 1 - v i * v i := by
      simpa [Pi.single_apply, Matrix.one_apply, vecMulVec] using hii
    have hs : v i * v i = 0 := sub_eq_self.mp hh.symm
    exact hi ((mul_eq_zero.mp hs).elim id id)
  have horder : orderOf g = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf g)
      (orderOf_dvd_of_pow_eq_one hg2) with h | h
    · exact False.elim (hgne (orderOf_eq_one_iff.mp h))
    · exact h
  exact ⟨g, hgE, horder, hgA⟩


theorem mem_centralizer_beta_of_acts_reflection
    {G : Type} [Group G] (B : Basis3 G 8) {b₀ g : G} (hB0 : B.b 0 = b₀)
    (v : Coords 8) (hgA : B.Acts g (1 - vecMulVec v v)) (horth : v 0 + v 1 = 0) :
    g ∈ centralizer ({b₀ * B.b 1} : Set G) := by
  let w : Coords 8 := Pi.single 0 1 + Pi.single 1 1
  have hzero : vecMulVec v v *ᵥ w = 0 := by
    dsimp only [w]
    rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    ext i
    change v i * v 0 + v i * v 1 = 0
    rw [← mul_add, horth, mul_zero]
  have hreflect : (1 - vecMulVec v v) *ᵥ w = w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hzero, sub_zero]
  have hwp : B.vec w = b₀ * B.b 1 := by
    dsimp only [w]
    rw [B.vec_add, B.vec_single, B.vec_single, hB0]
  have hfix : g * (b₀ * B.b 1) * g⁻¹ = b₀ * B.b 1 := by
    rw [← hwp, B.acts_vec hgA w, hreflect]
  apply mem_centralizer_singleton_iff.mpr
  calc
    g * (b₀ * B.b 1) = (g * (b₀ * B.b 1) * g⁻¹) * g := by group
    _ = (b₀ * B.b 1) * g := by rw [hfix]


theorem exists_tau_swap_involution_of_std_twD7
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    ∃ τ ∈ normalizer (E : Set G), τ ∈ centralizer ({b₀ * B.b 1} : Set G) ∧
      orderOf τ = 2 ∧ ∀ j : Fin 8, τ * B.b j * τ⁻¹ = B.b (Equiv.swap 0 1 j) := by
  let v : Coords 8 := Pi.single 0 1 - Pi.single 1 1
  have hw : wt v = 2 := ggQ2x_wt_sub_single 0 1 (by decide)
  obtain ⟨τ, hτE, hτorder, hτA⟩ :=
    exists_root_reflection_of_std_twD7 hstd B hB hrec v (Or.inl hw)
  have hτC : τ ∈ centralizer ({b₀ * B.b 1} : Set G) :=
    mem_centralizer_beta_of_acts_reflection B hB.2.1 v hτA
      (by simp [v])
  have hτswap : B.Acts τ (spMat (Equiv.swap 0 1) (fun _ => 1)) := by
    rw [swap_matrix_eq_one_sub 0 1 (by decide)]
    exact hτA
  refine ⟨τ, hτE, hτC, hτorder, ?_⟩
  intro j
  have hcol : (fun i => spMat (Equiv.swap 0 1) (fun _ => 1) i j) =
      Pi.single (Equiv.swap 0 1 j) 1 := by
    ext i
    simp [spMat, Pi.single_apply]
  rw [hτswap j, hcol, B.vec_single]

theorem exists_tau_swap_of_std_twD7 {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    (B : Basis3 G 8) (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    ∃ τ ∈ normalizer (E : Set G), τ ∈ centralizer ({b₀ * B.b 1} : Set G) ∧
      ∀ j : Fin 8, τ * B.b j * τ⁻¹ = B.b (Equiv.swap 0 1 j) := by
  obtain ⟨τ, hτE, hτC, -, hτpoint⟩ := exists_tau_swap_involution_of_std_twD7 hstd B hB hrec
  exact ⟨τ, hτE, hτC, hτpoint⟩

end CFSG.StandardType.FrameRoute.FS81
