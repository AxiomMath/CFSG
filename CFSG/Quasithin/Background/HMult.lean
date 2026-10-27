module

public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin.H.Mult

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix Kronecker

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def kronOneHom (k : ℕ) : Matrix ι ι K →* Matrix (Fin k × ι) (Fin k × ι) K where
  toFun M := (1 : Matrix (Fin k) (Fin k) K) ⊗ₖ M
  map_one' := Matrix.one_kronecker_one
  map_mul' M N := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

@[expose] def diagGL (k : ℕ) : GL ι K →* GL (Fin k × ι) K := Units.map (kronOneHom k)

@[expose] def diagSub (k : ℕ) (Γ : Subgroup (GL ι K)) : Subgroup (GL (Fin k × ι) K) :=
  Γ.map (diagGL k)

theorem diagGL_mulVec (k : ℕ) (γ : GL ι K) (v : Fin k × ι → K) (p : Fin k × ι) :
    (((diagGL k γ : GL (Fin k × ι) K) : Matrix (Fin k × ι) (Fin k × ι) K) *ᵥ v) p =
      ((γ : Matrix ι ι K) *ᵥ fun i => v (p.1, i)) p.2 := by
  simp only [diagGL, kronOneHom, Units.coe_map, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply, Ne.symm hb]
  · intro hp
    exact (hp (Finset.mem_univ p.1)).elim

theorem diagGL_injective (k : ℕ) [NeZero k] :
    Function.Injective (diagGL (ι := ι) (K := K) k) := by
  intro M N h
  ext i j
  have h' := congrArg (fun g : GL (Fin k × ι) K =>
    ((g : Matrix (Fin k × ι) (Fin k × ι) K) (0, i) (0, j))) h
  simpa [diagGL, kronOneHom, Matrix.kroneckerMap_apply, Matrix.one_apply] using h'

@[expose] def blockVec {k : ℕ} (j : Fin k) (x : ι → K) : Fin k × ι → K :=
  fun p => if p.1 = j then x p.2 else 0

theorem blockVec_add {k : ℕ} (j : Fin k) (x y : ι → K) :
    blockVec j (x + y) = blockVec j x + blockVec j y := by
  funext p
  by_cases h : p.1 = j <;> simp [blockVec, h]

theorem sum_blockVec {k : ℕ} (v : Fin k × ι → K) :
    (∑ j : Fin k, blockVec (ι := ι) j (fun i => v (j, i))) = v := by
  funext p
  rw [Finset.sum_apply, Finset.sum_eq_single p.1]
  · simp [blockVec]
  · intro b _ hb
    simp [blockVec, hb, Ne.symm hb]
  · intro hp
    exact (hp (Finset.mem_univ p.1)).elim

theorem diagGL_blockVec (k : ℕ) (γ : GL ι K) (j : Fin k) (x : ι → K) :
    ((diagGL k γ : GL (Fin k × ι) K) : Matrix (Fin k × ι) (Fin k × ι) K) *ᵥ
        blockVec j x = blockVec j ((γ : Matrix ι ι K) *ᵥ x) := by
  funext p
  rw [diagGL_mulVec]
  by_cases h : p.1 = j
  · simp [blockVec, h]
  · have hfun : (fun i => blockVec (k := k) j x (p.1, i)) = (0 : ι → K) := by
      funext i
      simp [blockVec, h]
    rw [hfun, Matrix.mulVec_zero]
    simp [blockVec, h]

@[expose] def lineSub {k : ℕ} (u : Fin k → K) : Subgroup (StdMod (Fin k × ι) K) where
  carrier := {v | ∃ x : ι → K, Multiplicative.toAdd v = fun p => u p.1 * x p.2}
  one_mem' := ⟨0, by funext p; simp⟩
  mul_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, by rw [toAdd_mul, hx, hy]; funext p; simp [mul_add]⟩
  inv_mem' := by
    rintro a ⟨x, hx⟩
    exact ⟨-x, by rw [toAdd_inv, hx]; funext p; simp⟩

@[expose] def lineEmb {k : ℕ} (u : Fin k → K) : StdMod ι K →* StdMod (Fin k × ι) K where
  toFun x := Multiplicative.ofAdd fun p => u p.1 * Multiplicative.toAdd x p.2
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext p
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext p
    simp [mul_add]

theorem lineEmb_toAdd {k : ℕ} (u : Fin k → K) (x : StdMod ι K) :
    Multiplicative.toAdd (lineEmb (ι := ι) u x) =
      fun p => u p.1 * Multiplicative.toAdd x p.2 := rfl

theorem lineEmb_injective {k : ℕ} {u : Fin k → K} (hu : u ≠ 0) :
    Function.Injective (lineEmb (ι := ι) u) := by
  intro x y h
  have h' : ∀ p : Fin k × ι, u p.1 * Multiplicative.toAdd x p.2 =
      u p.1 * Multiplicative.toAdd y p.2 := by
    intro p
    have hh := congrFun (congrArg Multiplicative.toAdd h) p
    change u p.1 * Multiplicative.toAdd x p.2 =
      u p.1 * Multiplicative.toAdd y p.2 at hh
    exact hh
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  apply Multiplicative.toAdd.injective
  funext i
  exact mul_left_cancel₀ hj (h' (j, i))

theorem range_lineEmb {k : ℕ} (u : Fin k → K) :
    (lineEmb (ι := ι) u).range = lineSub (ι := ι) u := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Multiplicative.toAdd x, rfl⟩
  · rintro ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [lineEmb_toAdd]
    exact hx.symm

private theorem diagGL_lineEmb {k : ℕ} (u : Fin k → K) (γ : GL ι K) (x : StdMod ι K) :
    matAut (diagGL k γ) (lineEmb (ι := ι) u x) =
      lineEmb (ι := ι) u (matAut γ x) := by
  apply Multiplicative.toAdd.injective
  funext p
  change toAddMap (matAut (diagGL k γ))
      (Multiplicative.toAdd (lineEmb (ι := ι) u x)) p =
    Multiplicative.toAdd (lineEmb (ι := ι) u (matAut γ x)) p
  rw [toAddMap_matAut, diagGL_mulVec, lineEmb_toAdd]
  have hx : Multiplicative.toAdd (matAut γ x) =
      ((γ : Matrix ι ι K) *ᵥ Multiplicative.toAdd x) := by
    simpa [toAddMap] using toAddMap_matAut (ι := ι) γ (Multiplicative.toAdd x)
  rw [lineEmb_toAdd, hx]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem exists_lineSub_equiv {k : ℕ} (u : Fin k → K) (hu : u ≠ 0) :
    ∃ e : ↥(lineSub (ι := ι) u) ≃* StdMod ι K,
      ∀ (γ : GL ι K) (w : ↥(lineSub (ι := ι) u))
        (h : matAut (diagGL k γ) (w : StdMod (Fin k × ι) K) ∈ lineSub (ι := ι) u),
        e ⟨_, h⟩ = matAut γ (e w) := by
  have hmem : ∀ x : StdMod ι K, lineEmb (ι := ι) u x ∈ lineSub (ι := ι) u := by
    intro x
    rw [← range_lineEmb]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  let φ : StdMod ι K →* ↥(lineSub (ι := ι) u) :=
    (lineEmb (ι := ι) u).codRestrict (lineSub (ι := ι) u) hmem
  have hφinj : Function.Injective φ := by
    intro x y h
    exact lineEmb_injective hu (Subtype.ext_iff.mp h)
  have hφsurj : Function.Surjective φ := by
    intro w
    obtain ⟨x, hx⟩ := w.2
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (lineEmb (ι := ι) u (Multiplicative.ofAdd x)) =
      Multiplicative.toAdd (w : StdMod (Fin k × ι) K)
    rw [lineEmb_toAdd]
    exact hx.symm
  let ψ : StdMod ι K ≃* ↥(lineSub (ι := ι) u) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hψ : ∀ x, (ψ x : StdMod (Fin k × ι) K) = lineEmb (ι := ι) u x := fun x => rfl
  refine ⟨ψ.symm, ?_⟩
  intro γ w h
  apply ψ.injective
  rw [ψ.apply_symm_apply]
  apply Subtype.ext
  change matAut (diagGL k γ) (w : StdMod (Fin k × ι) K) =
    (ψ (matAut γ (ψ.symm w)) : StdMod (Fin k × ι) K)
  rw [hψ]
  have hw : (w : StdMod (Fin k × ι) K) = lineEmb (ι := ι) u (ψ.symm w) := by
    rw [← hψ (ψ.symm w), ψ.apply_symm_apply]
  rw [hw, diagGL_lineEmb]

theorem normalForm_lineEmb {k : ℕ} {T : MulAut (StdMod (Fin k × ι) K)}
    {A : MulAut (StdMod ι K)} {σ : K ≃+* K} (hA : IsSemilinear A σ)
    {B : Matrix (Fin k) (Fin k) K}
    (hT : ∀ (v : Fin k × ι → K) (p : Fin k × ι), toAddMap T v p =
      toAddMap A (fun i => ∑ j, B p.1 j * v (j, i)) p.2) (u : Fin k → K) (x : StdMod ι K) :
    T (lineEmb (ι := ι) u x) = lineEmb (fun j => σ ((B *ᵥ u) j)) (A x) := by
  apply Multiplicative.toAdd.injective
  funext p
  change toAddMap T (Multiplicative.toAdd (lineEmb (ι := ι) u x)) p =
    Multiplicative.toAdd (lineEmb (fun j => σ ((B *ᵥ u) j)) (A x)) p
  rw [hT]
  have h1 : (fun i => ∑ j, B p.1 j * Multiplicative.toAdd (lineEmb (ι := ι) u x) (j, i)) =
      fun i => (∑ j, B p.1 j * u j) * Multiplicative.toAdd x i := by
    funext i
    rw [lineEmb_toAdd]
    simp only
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1]
  have h2 : (fun i => (∑ j, B p.1 j * u j) * Multiplicative.toAdd x i) =
      (∑ j, B p.1 j * u j) • Multiplicative.toAdd x := rfl
  rw [h2, hA, lineEmb_toAdd]
  have hx : Multiplicative.toAdd (A x) = toAddMap A (Multiplicative.toAdd x) := by
    simp [toAddMap, ofAdd_toAdd]
  rw [hx]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]

end CFSG.Quasithin.H.Mult

end
