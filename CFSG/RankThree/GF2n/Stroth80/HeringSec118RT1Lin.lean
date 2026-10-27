module

public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic CFSG.Open
open CFSG.Open.StatedAPI
open scoped Matrix

theorem rank_map_ringHom_le {K L : Type*} [Field K] [Field L] {m n : Type*} [Fintype m]
    [Fintype n] (σ : K →+* L) (B : Matrix m n K) : (B.map σ).rank ≤ B.rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  set W : Submodule K (m → K) := Submodule.span K (Set.range B.col) with hW
  let φ : (m → K) →ₛₗ[σ] (m → L) :=
    { toFun := fun v i => σ (v i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }
  let bW := Module.finBasis K W
  let s : Finset (m → L) := Finset.univ.image (fun l => φ (bW l : m → K))
  have hsub : Submodule.span L (Set.range (B.map σ).col)
      ≤ Submodule.span L (s : Set (m → L)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : B.col j ∈ W := Submodule.subset_span ⟨j, rfl⟩
    have hrepr := bW.sum_repr ⟨B.col j, hj⟩
    have hcol : B.col j = ∑ l, bW.repr ⟨B.col j, hj⟩ l • (bW l : m → K) := by
      have := congrArg (fun x : W => (x : m → K)) hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    have himg : (B.map σ).col j = φ (B.col j) := by
      ext i; rfl
    rw [himg, hcol, map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)))
  calc Module.finrank L (Submodule.span L (Set.range (B.map σ).col))
      ≤ Module.finrank L (Submodule.span L (s : Set (m → L))) := Submodule.finrank_mono hsub
    _ ≤ s.card := finrank_span_finset_le_card s
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Module.finrank K W := by simp

theorem rank_map_ringEquiv {K L : Type*} [Field K] [Field L] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (τ : K ≃+* L) (A : Matrix ι ι K) : (A.map τ).rank = A.rank := by
  refine le_antisymm (rank_map_ringHom_le (τ : K →+* L) A) ?_
  have h : ((A.map τ).map τ.symm).rank ≤ (A.map τ).rank :=
    rank_map_ringHom_le (τ.symm : L →+* K) (A.map τ)
  have hA : (A.map τ).map τ.symm = A := by
    ext i j
    simp
  rw [hA] at h
  exact h

section StatedSpMap

variable {m : ℕ} {K L : Type} [Field K] [Field L]

@[expose] noncomputable def statedSpMapEquiv (τ : K ≃+* L) : StatedSp m K ≃* StatedSp m L where
  toFun g := ⟨Matrix.GeneralLinearGroup.map (τ : K →+* L) (g : GL (Fin m ⊕ Fin m) K),
    map_mem_statedSp _ g.2⟩
  invFun g := ⟨Matrix.GeneralLinearGroup.map (τ.symm : L →+* K) (g : GL (Fin m ⊕ Fin m) L),
    map_mem_statedSp _ g.2⟩
  left_inv g := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    simp
  right_inv g := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    simp
  map_mul' g h := Subtype.ext (map_mul (Matrix.GeneralLinearGroup.map (τ : K →+* L)) _ _)

theorem coe_statedSpMapEquiv (τ : K ≃+* L) (g : StatedSp m K) :
    (((statedSpMapEquiv τ g : StatedSp m L) : GL (Fin m ⊕ Fin m) L) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) =
      ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map τ := rfl

end StatedSpMap

section RankOne

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private theorem dotProduct_row_of_linear (f : (ι → K) →ₗ[K] K) :
    ∃ γ : ι → K, ∀ x, f x = γ ⬝ᵥ x := by
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun x => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  simp only [dotProduct, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq ι] in
private theorem vecMulVec_mulVec_eq_smul (p r x : ι → K) :
    Matrix.vecMulVec p r *ᵥ x = (r ⬝ᵥ x) • p := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

private theorem exists_vecMulVec_of_rank_sub_one {M : Matrix ι ι K} (h : (M - 1).rank = 1) :
    ∃ p r : ι → K, p ≠ 0 ∧ r ≠ 0 ∧ M = 1 + Matrix.vecMulVec p r := by
  set N := M - 1 with hNdef
  have hfin : Module.finrank K (LinearMap.range N.mulVecLin) = 1 := h
  obtain ⟨v, hv⟩ : ∃ v : LinearMap.range N.mulVecLin, v ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hfin]; exact Nat.one_pos)
  have hspan := (finrank_eq_one_iff_of_nonzero' v hv).mp hfin
  set p : ι → K := (v : ι → K) with hpdef
  have hp : p ≠ 0 := by
    intro h0
    apply hv
    exact Subtype.ext h0
  have hmem : ∀ x, N *ᵥ x ∈ LinearMap.range N.mulVecLin := fun x =>
    LinearMap.mem_range_self N.mulVecLin x
  choose c hc using fun x => hspan ⟨N *ᵥ x, hmem x⟩
  have hc' : ∀ x, c x • p = N *ᵥ x := fun x => by
    simpa [hpdef] using congrArg Subtype.val (hc x)
  have hadd : ∀ x y, c (x + y) = c x + c y := by
    intro x y
    apply smul_left_injective K hp
    simp only [add_smul]
    rw [hc', hc', hc', Matrix.mulVec_add]
  have hsmul : ∀ (a : K) x, c (a • x) = a * c x := by
    intro a x
    apply smul_left_injective K hp
    simp only
    rw [mul_smul, hc', hc', Matrix.mulVec_smul]
  let f : (ι → K) →ₗ[K] K :=
    { toFun := c
      map_add' := hadd
      map_smul' := fun a x => by simpa using hsmul a x }
  obtain ⟨r, hr⟩ := dotProduct_row_of_linear f
  have hNeq : N = Matrix.vecMulVec p r := by
    refine Matrix.ext_iff_mulVec.mpr fun x => ?_
    rw [vecMulVec_mulVec_eq_smul, ← hc' x]
    have hcx : c x = r ⬝ᵥ x := hr x
    rw [hcx]
  have hr0 : r ≠ 0 := by
    intro hr0
    have hN0 : N = 0 := by rw [hNeq, hr0, Matrix.vecMulVec_zero]
    rw [hN0, Matrix.rank_zero] at h
    exact absurd h (by norm_num)
  refine ⟨p, r, hp, hr0, ?_⟩
  rw [← hNeq, hNdef]
  abel

end RankOne

theorem exists_mulVec_eq_of_rank_eq_one {m : ℕ} {K : Type} [Field K] (g : StatedSp m K)
    (hr : Matrix.rank (((g : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) = 1) :
    ∃ (u : Fin m ⊕ Fin m → K) (c : K), u ≠ 0 ∧ c ≠ 0 ∧ ∀ x : Fin m ⊕ Fin m → K,
      ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
        x + (c * spForm m K x u) • u := by
  obtain ⟨p, r, hp, hr0, hA⟩ := exists_vecMulVec_of_rank_sub_one hr
  have hpres := (mem_statedSp_iff_forall (g : GL (Fin m ⊕ Fin m) K)).mp g.2
  have hmv : ∀ x : Fin m ⊕ Fin m → K,
      ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
        x + (r ⬝ᵥ x) • p := by
    intro x
    rw [hA, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec_eq_smul]
  have hkey : ∀ x y : Fin m ⊕ Fin m → K,
      (r ⬝ᵥ y) * spForm m K x p = (r ⬝ᵥ x) * spForm m K y p := by
    intro x y
    have h := hpres x y
    rw [hmv x, hmv y] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_self, mul_zero, add_zero] at h
    have hpy : spForm m K p y = -spForm m K y p :=
      ((spForm_isAlt (m := m) (K := K)).neg_eq y p).symm
    rw [hpy] at h
    linear_combination h
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin m ⊕ Fin m → K, spForm m K y₀ p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hp ((spForm_nondegenerate (m := m) (K := K)).2 p hcon)
  set c : K := (r ⬝ᵥ y₀) / spForm m K y₀ p with hcdef
  have hrx : ∀ x : Fin m ⊕ Fin m → K, r ⬝ᵥ x = c * spForm m K x p := by
    intro x
    rw [hcdef, div_mul_eq_mul_div, eq_div_iff hy₀]
    exact (hkey x y₀).symm
  have hc0 : c ≠ 0 := by
    intro h0
    apply hr0
    funext i
    have h1 := hrx (Pi.single i 1)
    rw [h0, zero_mul, dotProduct_single, mul_one] at h1
    simpa using h1
  refine ⟨p, c, hp, hc0, fun x => ?_⟩
  rw [hmv x, hrx x]

theorem exists_spEquiv_eq_Tsp_of_rank_eq_one {m : ℕ} {K : Type} [Field K] (g : StatedSp m K)
    (hr : Matrix.rank (((g : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) = 1) :
    ∃ (u : Fin m ⊕ Fin m → K) (c : K), u ≠ 0 ∧ c ≠ 0 ∧
      spEquiv g = Tsp (spForm_isAlt (m := m) (K := K)) u c := by
  obtain ⟨u, c, hu, hc, hx⟩ := exists_mulVec_eq_of_rank_eq_one g hr
  refine ⟨u, c, hu, hc, Gsp.ext' fun x => ?_⟩
  rw [spEquiv_app, Tsp_app]
  exact hx x

end CFSG.RankThree.GF2n.Stroth80
