module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.StandardType.RCKRP

open CFSG.StandardType.ClassicalPosition

private theorem rckRPgc_one_add_smul_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {N : Matrix ι ι F} (hN : N * N = 0) (a b : F) :
    (1 + a • N) * (1 + b • N) = 1 + (a + b) • N := by
  have h : (a • N) * (b • N) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN, smul_zero]
  have hmain : (1 + a • N) * (1 + b • N) =
      (1 + a • N) + (b • N + (a • N) * (b • N)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  calc (1 + a • N) * (1 + b • N)
      = (1 + a • N) + (b • N + (a • N) * (b • N)) := hmain
    _ = (1 + a • N) + b • N := by rw [h, add_zero]
    _ = 1 + (a • N + b • N) := by rw [add_assoc]
    _ = 1 + (a + b) • N := by rw [add_smul]

private theorem rckRPgc_one_add_smul_mul_neg {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {N : Matrix ι ι F} (hN : N * N = 0) (c : F) :
    (1 + c • N) * (1 + (-c) • N) = 1 := by
  rw [rckRPgc_one_add_smul_mul hN]
  simp

private theorem rckRPgc_one_add_smul_neg_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {N : Matrix ι ι F} (hN : N * N = 0) (c : F) :
    (1 + (-c) • N) * (1 + c • N) = 1 := by
  rw [rckRPgc_one_add_smul_mul hN]
  simp

private def rckRPgc_one_add_smul_unit {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {N : Matrix ι ι F} (hN : N * N = 0) (c : F) : GL ι F :=
  Units.mk (1 + c • N) (1 + (-c) • N)
    (rckRPgc_one_add_smul_mul_neg hN c) (rckRPgc_one_add_smul_neg_mul hN c)

private theorem rckRPgc_one_add_smul_unit_val {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {N : Matrix ι ι F} (hN : N * N = 0) (c : F) :
    (rckRPgc_one_add_smul_unit hN c : Matrix ι ι F) = 1 + c • N :=
  rfl

private theorem rckRPgc_one_add_smul_unit_injective {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {N : Matrix ι ι F} (hN : N * N = 0) (hN0 : N ≠ 0) :
    Function.Injective (fun c : F => rckRPgc_one_add_smul_unit hN c) := by
  intro a b hab
  have h : a • N = b • N := by
    have h' : (1 : Matrix ι ι F) + a • N = 1 + b • N := by
      simpa only [rckRPgc_one_add_smul_unit_val] using
        congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hab
    exact add_left_cancel h'
  by_contra hne
  apply hN0
  have hsub : (a - b) • N = 0 := by rw [sub_smul, h, sub_self]
  calc N = 1 • N := (one_smul F N).symm
    _ = ((a - b)⁻¹ * (a - b)) • N := by rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne)]
    _ = (a - b)⁻¹ • ((a - b) • N) := by rw [smul_smul]
    _ = 0 := by rw [hsub, smul_zero]

private def rckRPgc_one_add_smul_subgroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {N : Matrix ι ι F} (hN : N * N = 0) {A : Set F} (h0 : (0 : F) ∈ A)
    (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A) (hneg : ∀ a ∈ A, -a ∈ A) :
    Subgroup (GL ι F) where
  carrier := {g | ∃ c ∈ A, (g : Matrix ι ι F) = 1 + c • N}
  mul_mem' := by
    rintro g h ⟨a, ha, hga⟩ ⟨b, hb, hgb⟩
    refine ⟨a + b, hadd a ha b hb, ?_⟩
    rw [Units.val_mul, hga, hgb, rckRPgc_one_add_smul_mul hN]
  one_mem' := ⟨0, h0, by rw [zero_smul, add_zero, Units.val_one]⟩
  inv_mem' := by
    rintro g ⟨a, ha, hga⟩
    refine ⟨-a, hneg a ha, ?_⟩
    have hmul : g * rckRPgc_one_add_smul_unit hN (-a) = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one, hga, rckRPgc_one_add_smul_unit_val]
      exact rckRPgc_one_add_smul_mul_neg hN a
    rw [inv_eq_of_mul_eq_one_right hmul, rckRPgc_one_add_smul_unit_val]

private theorem rckRPgc_natCard_closure_one_add_smul {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {N : Matrix ι ι F} (hN : N * N = 0) (hN0 : N ≠ 0) {A : Set F}
    (h0 : (0 : F) ∈ A) (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ A)
    (hneg : ∀ a ∈ A, -a ∈ A) :
    Nat.card (Subgroup.closure {g : GL ι F | ∃ c ∈ A, (g : Matrix ι ι F) = 1 + c • N}) =
      Nat.card A := by
  have hH : Subgroup.closure {g : GL ι F | ∃ c ∈ A, (g : Matrix ι ι F) = 1 + c • N} =
      rckRPgc_one_add_smul_subgroup hN h0 hadd hneg := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      exact hg
    · intro g hg
      exact Subgroup.subset_closure hg
  rw [hH]
  refine Nat.card_congr (Equiv.ofBijective (fun c : A =>
    (⟨rckRPgc_one_add_smul_unit hN c.1,
      ⟨c.1, c.2, rckRPgc_one_add_smul_unit_val hN c.1⟩⟩ :
      rckRPgc_one_add_smul_subgroup hN h0 hadd hneg)) ⟨?_, ?_⟩).symm
  · intro c d hcd
    have h1 : rckRPgc_one_add_smul_unit hN c.1 = rckRPgc_one_add_smul_unit hN d.1 :=
      congrArg (fun x : rckRPgc_one_add_smul_subgroup hN h0 hadd hneg => (x : GL ι F)) hcd
    exact Subtype.ext (rckRPgc_one_add_smul_unit_injective hN hN0 h1)
  · rintro ⟨g, hg⟩
    change ∃ c ∈ A, (g : Matrix ι ι F) = 1 + c • N at hg
    obtain ⟨c, hcA, hcg⟩ := hg
    refine ⟨⟨c, hcA⟩, Subtype.ext ?_⟩
    exact Units.ext (by rw [rckRPgc_one_add_smul_unit_val]; exact hcg.symm)

theorem card_matTransvGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    {v φ : ι → F} (hv : v ≠ 0) (hφ : φ ≠ 0) (hvφ : φ ⬝ᵥ v = 0) :
    Nat.card (matTransvGroup v φ) = Nat.card F := by
  have hN : Matrix.vecMulVec v φ * Matrix.vecMulVec v φ = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, hvφ, zero_smul]
  have hN0 : Matrix.vecMulVec v φ ≠ 0 := by
    intro hzero
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hc
      exact hv (funext fun i => by by_contra h; exact hc ⟨i, h⟩)
    obtain ⟨j, hj⟩ : ∃ j, φ j ≠ 0 := by
      by_contra hc
      exact hφ (funext fun j => by by_contra h; exact hc ⟨j, h⟩)
    have hij : Matrix.vecMulVec v φ i j = 0 := by simp [hzero]
    rw [Matrix.vecMulVec_apply] at hij
    exact mul_ne_zero hi hj hij
  have hgen : {g : GL ι F | ∃ c : F, (g : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v φ} =
      {g : GL ι F | ∃ c ∈ (Set.univ : Set F),
        (g : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v φ} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and]
  rw [matTransvGroup, hgen]
  rw [rckRPgc_natCard_closure_one_add_smul (A := Set.univ) hN hN0 (by simp)
    (by intro a _ b _; trivial) (by intro a _; trivial)]
  exact Nat.card_univ

private theorem rckRPgc_altSiegel_ne_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (hG : IsUnit G.det) {v w : ι → F}
    (hli : LinearIndependent F ![v, w]) :
    Matrix.vecMulVec v (G.mulVec w) + Matrix.vecMulVec w (G.mulVec v) ≠ 0 := by
  intro hzero
  have hw0 : w ≠ 0 := by simpa using hli.ne_zero 1
  have hmulv : Function.Injective (fun x : ι → F => G.mulVec x) :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det G).mpr hG)
  have ha0 : G.mulVec w ≠ 0 := by
    intro hh
    apply hw0
    have hw : G.mulVec w = G.mulVec 0 := by rw [hh]; simp
    exact hmulv hw
  have hrel : ∀ j, (G.mulVec w) j • v + (G.mulVec v) j • w = 0 := by
    intro j
    funext i
    have h0 : (Matrix.vecMulVec v (G.mulVec w) +
        Matrix.vecMulVec w (G.mulVec v)) i j = 0 := by
      rw [hzero, Matrix.zero_apply]
    rw [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply] at h0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm ((G.mulVec w) j) (v i), mul_comm ((G.mulVec v) j) (w i)]
    exact h0
  have hcoef : ∀ j, (G.mulVec w) j = 0 := by
    intro j
    have hsum : (∑ i : Fin 2,
        ![(G.mulVec w) j, (G.mulVec v) j] i • ![v, w] i) = 0 := by
      simpa [Fin.sum_univ_two] using hrel j
    have h0 := (Fintype.linearIndependent_iff (R := F) (v := ![v, w])).mp hli
      ![(G.mulVec w) j, (G.mulVec v) j] hsum 0
    simpa using h0
  exact ha0 (funext hcoef)

theorem card_altSiegelGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] {G : Matrix ι ι F} (hG : IsUnit G.det) (hsymm : G.transpose = G)
    (halt : ∀ x : ι → F, x ⬝ᵥ G.mulVec x = 0) {v w : ι → F}
    (hli : LinearIndependent F ![v, w]) (hvw : v ⬝ᵥ G.mulVec w = 0) :
    Nat.card (altSiegelGroup G v w) = Nat.card F := by
  set N : Matrix ι ι F :=
    Matrix.vecMulVec v (G.mulVec w) + Matrix.vecMulVec w (G.mulVec v) with hNdef
  have hsym : ∀ x y : ι → F, x ⬝ᵥ G.mulVec y = y ⬝ᵥ G.mulVec x := by
    intro x y
    have h := Matrix.dotProduct_transpose_mulVec G y x
    rw [hsymm] at h
    exact h.symm
  have h1 : G.mulVec w ⬝ᵥ v = 0 := by rw [dotProduct_comm, hvw]
  have h2 : G.mulVec w ⬝ᵥ w = 0 := by rw [dotProduct_comm, halt w]
  have h3 : G.mulVec v ⬝ᵥ v = 0 := by rw [dotProduct_comm, halt v]
  have h4 : G.mulVec v ⬝ᵥ w = 0 := by rw [dotProduct_comm, hsym w v, hvw]
  have hN : N * N = 0 := by
    rw [hNdef, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
      Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
      Matrix.vecMulVec_smul, Matrix.vecMulVec_smul, Matrix.vecMulVec_smul,
      Matrix.vecMulVec_smul, h1, h2, h3, h4]
    simp
  have hN0 : N ≠ 0 := by
    rw [hNdef]
    exact rckRPgc_altSiegel_ne_zero hG hli
  have hgen : {g : GL ι F | ∃ c : F, (g : Matrix ι ι F) = 1 + c •
        (Matrix.vecMulVec v (G.mulVec w) + Matrix.vecMulVec w (G.mulVec v))} =
      {g : GL ι F | ∃ c ∈ (Set.univ : Set F), (g : Matrix ι ι F) = 1 + c • N} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, hNdef]
  rw [altSiegelGroup, hgen]
  rw [rckRPgc_natCard_closure_one_add_smul (A := Set.univ) hN hN0 (by simp)
    (by intro x _ y _; trivial) (by intro x _; trivial)]
  exact Nat.card_univ

private theorem rckRPgc_unitTransv_ne_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (hσ : Function.Injective σ) {G : Matrix ι ι F} (hG : IsUnit G.det)
    {v : ι → F} (hv : v ≠ 0) :
    Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) ≠ 0 := by
  intro hzero
  have hx0 : (fun i => σ (v i)) ≠ 0 := by
    intro h
    apply hv
    funext i
    have hi : σ (v i) = 0 := by simpa using congrFun h i
    have hz : σ (v i) = σ 0 := by simp [hi]
    exact hσ hz
  have ha0 : Matrix.vecMul (fun i => σ (v i)) G ≠ 0 := by
    intro h
    have hinj : Function.Injective (fun x : ι → F => Matrix.vecMul x G) :=
      Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det G).mpr hG)
    have hx : (fun i => σ (v i)) = 0 := by
      apply hinj
      simpa using h
    exact hx0 hx
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    exact hv (funext fun i => by by_contra h; exact hc ⟨i, h⟩)
  obtain ⟨j, hj⟩ : ∃ j, Matrix.vecMul (fun i => σ (v i)) G j ≠ 0 := by
    by_contra hc
    exact ha0 (funext fun j => by by_contra h; exact hc ⟨j, h⟩)
  have hij : Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) i j = 0 := by
    simp [hzero]
  rw [Matrix.vecMulVec_apply] at hij
  exact mul_ne_zero hi hj hij

theorem card_unitTransvGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) {v : ι → F} (hv : v ≠ 0)
    (hiso : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ v = 0) :
    Nat.card (unitTransvGroup σ G v) = Nat.card {c : F // σ c = c} := by
  have hσinj : Function.Injective σ := by
    intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h0 : σ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 : σ ((x - y)⁻¹ * (x - y)) = 1 := by rw [inv_mul_cancel₀ hsub, map_one]
    rw [map_mul, h0, mul_zero] at h1
    exact zero_ne_one h1
  have hN : Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) *
      Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, hiso, zero_smul]
  have hN0 : Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) ≠ 0 :=
    rckRPgc_unitTransv_ne_zero σ hσinj hG hv
  have hgen : {g : GL ι F | ∃ c : F, σ c = c ∧ (g : Matrix ι ι F) =
        1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G)} =
      {g : GL ι F | ∃ c ∈ {c : F | σ c = c}, (g : Matrix ι ι F) =
        1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G)} := by
    ext g
    simp
  rw [unitTransvGroup, hgen]
  rw [rckRPgc_natCard_closure_one_add_smul (A := {c : F | σ c = c}) hN hN0 (by simp)
    (by intro x hx y hy; simp only [Set.mem_setOf_eq] at *; rw [map_add, hx, hy])
    (by intro x hx; simp only [Set.mem_setOf_eq] at *; rw [map_neg, hx])]
  rfl

end CFSG.StandardType.RCKRP
