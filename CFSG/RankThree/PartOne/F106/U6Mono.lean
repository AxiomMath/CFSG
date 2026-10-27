module

public import Certificates.Data.U6ThreeRank
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix CFSG.Assembly.LowTwoRank

theorem u6Perm_apply (t : Fin 2 → ZMod 3) (i : Fin 6) :
    u6Perm t i = u6Idx.symm ((u6Idx i).1, (u6Idx i).2 + t (u6Idx i).1) := rfl

theorem u6Perm_zero : u6Perm 0 = 1 := by
  ext i
  simp [u6Perm_apply]

theorem u6Perm_add (t t' : Fin 2 → ZMod 3) : u6Perm (t + t') = u6Perm t * u6Perm t' := by
  ext i
  simp only [u6Perm_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Pi.add_apply]
  simp only [add_assoc, add_comm (t' _) (t _)]

theorem u6Perm_neg (t : Fin 2 → ZMod 3) : u6Perm (-t) = (u6Perm t)⁻¹ := by
  have hneg : ∀ x : ZMod 3, -x + x = 0 := by decide
  have h0 : (-t + t : Fin 2 → ZMod 3) = 0 := funext fun s => hneg (t s)
  rw [eq_inv_iff_mul_eq_one, ← u6Perm_add, h0, u6Perm_zero]

theorem u6Perm_injective {t t' : Fin 2 → ZMod 3} (h : u6Perm t = u6Perm t') : t = t' := by
  funext s
  have h0 := congrArg (fun σ => u6Idx (σ (u6Idx.symm (s, 0)))) h
  simpa [u6Perm_apply] using h0

structure Cube (K : Type) [Field K] where
  ω : K
  cube : ω ^ 3 = 1
  ne_one : ω ≠ 1

namespace Cube

variable {K : Type} [Field K] (c : Cube K)

@[expose] def p (a : ZMod 3) : K := c.ω ^ a.val

theorem p_zero : c.p 0 = 1 := by simp [p]

theorem ω_ne_zero : c.ω ≠ 0 := fun h => by simpa [h] using c.cube

theorem p_ne_zero (a : ZMod 3) : c.p a ≠ 0 := pow_ne_zero _ c.ω_ne_zero

theorem p_add (a b : ZMod 3) : c.p (a + b) = c.p a * c.p b := by
  unfold p
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) 3, pow_add, pow_mul, c.cube, one_pow, mul_one]

theorem p_pow_three (a : ZMod 3) : c.p a ^ 3 = 1 := by
  unfold p
  rw [← pow_mul, mul_comm, pow_mul, c.cube, one_pow]

theorem p_eq_one {a : ZMod 3} (h : c.p a = 1) : a = 0 := by
  have hcases : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  rcases hcases a with rfl | rfl | rfl
  · rfl
  · exfalso
    apply c.ne_one
    rw [p, show (1 : ZMod 3).val = 1 from rfl, pow_one] at h
    exact h
  · exfalso
    apply c.ne_one
    have h2 : c.ω ^ 2 = 1 := by
      rw [p, show (2 : ZMod 3).val = 2 from rfl] at h
      exact h
    calc c.ω = c.ω * c.ω ^ 2 := by rw [h2, mul_one]
      _ = 1 := by rw [← pow_succ']; exact c.cube

theorem p_injective {a b : ZMod 3} (h : c.p a = c.p b) : a = b := by
  have h1 : c.p (a - b) * c.p b = c.p b := by
    rw [← c.p_add, sub_add_cancel, h]
  have h2 : c.p (a - b) = 1 := by
    have := c.p_ne_zero b
    exact mul_right_cancel₀ this (by rw [h1, one_mul])
  exact sub_eq_zero.1 (c.p_eq_one h2)

theorem prod_p {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ZMod 3) :
    ∏ i ∈ s, c.p (d i) = c.p (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty => simp [c.p_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, c.p_add, ih]

@[expose] def mono (d : Fin 6 → ZMod 3) (σ : Equiv.Perm (Fin 6)) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun i j => if i = σ j then c.p (d i) else 0

theorem mono_mul (d d' : Fin 6 → ZMod 3) (σ σ' : Equiv.Perm (Fin 6)) :
    c.mono d σ * c.mono d' σ' = c.mono (fun i => d i + d' (σ⁻¹ i)) (σ * σ') := by
  ext i k
  simp only [Matrix.mul_apply, mono, Matrix.of_apply, Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (σ' k)]
  · by_cases h : i = σ (σ' k)
    · subst h
      simp [c.p_add]
    · simp [h]
  · intro j _ hj
    simp [hj]
  · simp

theorem mono_one : c.mono 0 1 = (1 : Matrix (Fin 6) (Fin 6) K) := by
  ext i j
  simp [mono, Matrix.one_apply, c.p_zero]

theorem mono_add_const (d : Fin 6 → ZMod 3) (σ : Equiv.Perm (Fin 6)) (e : ZMod 3) :
    c.mono (fun i => d i + e) σ = c.p e • c.mono d σ := by
  ext i j
  simp only [mono, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [c.p_add, mul_comm]
  · simp

theorem mono_unitary (d : Fin 6 → ZMod 3) (σ : Equiv.Perm (Fin 6)) :
    ((c.mono d σ).map (· ^ 2 ^ 1))ᵀ * c.mono d σ = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mono, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (σ a)]
  · by_cases h : a = b
    · subst h
      have h3 := c.p_pow_three (d (σ a))
      simp
      linear_combination h3
    · simp [h, σ.injective.ne h]
  · intro i _ hi
    simp [hi]
  · simp

theorem mono_eq_smul {d d' : Fin 6 → ZMod 3} {σ σ' : Equiv.Perm (Fin 6)} {u : K}
    (h : c.mono d' σ' = u • c.mono d σ) : σ' = σ ∧ ∀ i, c.p (d' i) = u * c.p (d i) := by
  have hσ : ∀ j, σ' j = σ j := by
    intro j
    have h1 := congrFun (congrFun h (σ' j)) j
    simp only [mono, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at h1
    by_contra hne
    simp [hne] at h1
    exact c.p_ne_zero _ h1
  have hσ' : σ' = σ := Equiv.ext hσ
  refine ⟨hσ', fun i => ?_⟩
  have h1 := congrFun (congrFun h i) (σ⁻¹ i)
  simp only [mono, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hσ'] at h1
  simpa using h1

theorem det_mono [CharP K 2] (d : Fin 6 → ZMod 3) (σ : Equiv.Perm (Fin 6)) :
    (c.mono d σ).det = c.p (∑ i, d i) := by
  have hm : c.mono d σ = (Matrix.diagonal fun i => c.p (d i)).submatrix id σ := by
    ext i j
    simp [mono, Matrix.diagonal_apply]
  rw [hm, Matrix.det_permute', Matrix.det_diagonal, c.prod_p]
  have hs : ((Equiv.Perm.sign σ : ℤˣ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simp [h]
    · simp [h, CharTwo.neg_eq]
  rw [hs, one_mul]

theorem zadd_neg : ∀ x : ZMod 3, x + -x = 0 := by decide

theorem zneg_add : ∀ x : ZMod 3, -x + x = 0 := by decide

@[expose] def monoGL (d : Fin 6 → ZMod 3) (σ : Equiv.Perm (Fin 6)) : GL (Fin 6) K where
  val := c.mono d σ
  inv := c.mono (fun i => -d (σ i)) σ⁻¹
  val_inv := by
    rw [mono_mul]
    have h0 : (fun i => d i + (fun i => -d (σ i)) (σ⁻¹ i)) = 0 := by
      funext i
      have := zadd_neg (d i)
      simpa using this
    rw [h0, mul_inv_cancel, c.mono_one]
  inv_val := by
    rw [mono_mul]
    have h0 : (fun i => (fun i => -d (σ i)) i + d (σ⁻¹⁻¹ i)) = 0 := by
      funext i
      have := zneg_add (d (σ i))
      simpa using this
    rw [h0, inv_mul_cancel, c.mono_one]

theorem monoGL_val (d : Fin 6 → ZMod 3) (σ : Equiv.Perm (Fin 6)) :
    ((c.monoGL d σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = c.mono d σ := rfl

@[expose] noncomputable def scalGL (a : ZMod 3) : GL (Fin 6) K :=
  Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 (c.p a) (c.p_ne_zero a))

end Cube

namespace U6Mon

theorem d_ofFun (f : Fin 6 → ZMod 3) (s : Fin 2 → ZMod 3) : (ofFun f s).d = f := by
  funext i
  fin_cases i <;> rfl

theorem t_ofFun (f : Fin 6 → ZMod 3) (s : Fin 2 → ZMod 3) : (ofFun f s).t = s := by
  funext i
  fin_cases i <;> rfl

theorem ext' {x y : U6Mon} (hd : x.d = y.d) (ht : x.t = y.t) : x = y := by
  cases x
  cases y
  have h0 := congrFun hd 0
  have h1 := congrFun hd 1
  have h2 := congrFun hd 2
  have h3 := congrFun hd 3
  have h4 := congrFun hd 4
  have h5 := congrFun hd 5
  have g0 := congrFun ht 0
  have g1 := congrFun ht 1
  simp only [d, t, Matrix.cons_val_zero, Matrix.cons_val_one] at *
  simp_all

@[expose] def Ok (x : U6Mon) : Prop := x.d 0 = 0 ∧ ∑ i, x.d i = 0

theorem ok_one : one.Ok := by
  unfold one Ok
  rw [d_ofFun]
  simp

theorem ok_mul {x y : U6Mon} (hx : x.Ok) (hy : y.Ok) : (x.mul y).Ok := by
  unfold mul Ok
  rw [d_ofFun]
  refine ⟨sub_self _, ?_⟩
  have hperm : ∑ i, y.d (u6Perm (-x.t) i) = ∑ i, y.d i := Equiv.sum_comp _ _
  have hsum : ∑ i, x.raw y i = 0 := by
    have h1 : ∑ i, x.raw y i = ∑ i, x.d i + ∑ i, y.d (u6Perm (-x.t) i) :=
      Finset.sum_add_distrib
    rw [h1, hperm, hx.2, hy.2]
    exact add_zero _
  have h2 : ∑ i, (x.raw y i - x.raw y 0) = ∑ i, x.raw y i - ∑ _i : Fin 6, x.raw y 0 :=
    Finset.sum_sub_distrib _ _
  rw [h2, hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h6 : ((6 : ℕ) : ZMod 3) = 0 := by decide
  rw [h6, zero_mul]
  exact sub_self _

theorem ok_gen (k : ℕ) : (gen k).Ok := by
  by_cases hk : k < 6
  · interval_cases k <;> (unfold Ok; decide)
  · have h4 : ¬ k < 4 := by omega
    have h4' : k ≠ 4 := by omega
    have h5 : k ≠ 5 := by omega
    simp only [gen, h4, h4', h5, ↓reduceIte]
    exact ok_one

theorem ok_foldl {w : List U6Mon} (hw : ∀ g ∈ w, g.Ok) {a : U6Mon} (ha : a.Ok) :
    (w.foldl mul a).Ok := by
  induction w generalizing a with
  | nil => exact ha
  | cons g w ih =>
    exact ih (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg'))
      (ok_mul ha (hw g List.mem_cons_self))

theorem ok_evalWord (w : List ℕ) : (evalWord w).Ok :=
  ok_foldl (fun g hg => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    exact ok_gen k) ok_one

end U6Mon

namespace Cube

variable {K : Type} [Field K] (c : Cube K)

theorem zsub_add : ∀ a b : ZMod 3, a - b + b = a := by decide

theorem mono_mul_scalar (d : Fin 6 → ZMod 3) (σ : Equiv.Perm (Fin 6)) (a : K) :
    c.mono d σ * Matrix.scalar (Fin 6) a = a • c.mono d σ := by
  ext i j
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

@[expose] def monoC (x : U6Mon) : GL (Fin 6) K := c.monoGL x.d (u6Perm x.t)

theorem monoC_mul (x y : U6Mon) :
    c.monoC x * c.monoC y = c.monoC (x.mul y) * c.scalGL (x.raw y 0) := by
  apply Units.ext
  have hσ : (u6Perm x.t)⁻¹ = u6Perm (-x.t) := (u6Perm_neg x.t).symm
  have hraw : (fun i => (x.raw y i - x.raw y 0) + x.raw y 0) = x.raw y :=
    funext fun i => zsub_add _ _
  have hL : c.mono x.d (u6Perm x.t) * c.mono y.d (u6Perm y.t) =
      c.mono (x.raw y) (u6Perm (x.t + y.t)) := by
    rw [mono_mul, hσ, u6Perm_add]
    rfl
  have hR : c.mono (x.mul y).d (u6Perm (x.mul y).t) * Matrix.scalar (Fin 6) (c.p (x.raw y 0)) =
      c.mono (x.raw y) (u6Perm (x.t + y.t)) := by
    rw [mono_mul_scalar]
    have hd : (x.mul y).d = fun i => x.raw y i - x.raw y 0 := U6Mon.d_ofFun _ _
    have ht : (x.mul y).t = x.t + y.t := U6Mon.t_ofFun _ _
    rw [hd, ht, ← mono_add_const, hraw]
  rw [Units.val_mul, Units.val_mul]
  exact hL.trans hR.symm

theorem monoC_one : c.monoC U6Mon.one = 1 := by
  apply Units.ext
  have hd : U6Mon.one.d = fun _ => 0 := U6Mon.d_ofFun _ _
  have ht : U6Mon.one.t = fun _ => 0 := U6Mon.t_ofFun _ _
  show c.mono U6Mon.one.d (u6Perm U6Mon.one.t) = 1
  rw [hd, ht]
  have h0 : (fun _ : Fin 2 => (0 : ZMod 3)) = 0 := rfl
  have h1 : (fun _ : Fin 6 => (0 : ZMod 3)) = 0 := rfl
  rw [h0, h1, u6Perm_zero, c.mono_one]

section Mu

variable [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)

include hK

theorem monoC_mem {x : U6Mon} (hx : x.Ok) : c.monoC x ∈ StatedSU 6 (2 ^ 1) K := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 6) (by norm_num)).1
  rw [← SetLike.mem_coe, h]
  refine ⟨?_, c.mono_unitary _ _⟩
  show (c.mono x.d (u6Perm x.t)).det = 1
  rw [c.det_mono, hx.2, c.p_zero]

open scoped _root_.Classical in
@[expose] noncomputable def mu (x : U6Mon) : StatedProj (StatedSU 6 (2 ^ 1) K) :=
  if h : x.Ok then
    QuotientGroup.mk (⟨c.monoC x, c.monoC_mem hK h⟩ : StatedSU 6 (2 ^ 1) K)
  else 1

theorem mu_of_ok {x : U6Mon} (hx : x.Ok) :
    c.mu hK x = QuotientGroup.mk (⟨c.monoC x, c.monoC_mem hK hx⟩ : StatedSU 6 (2 ^ 1) K) := by
  simp [mu, hx]

theorem mu_mul {x y : U6Mon} (hx : x.Ok) (hy : y.Ok) :
    c.mu hK x * c.mu hK y = c.mu hK (x.mul y) := by
  have hxy := U6Mon.ok_mul hx hy
  rw [mu_of_ok c hK hx, mu_of_ok c hK hy, mu_of_ok c hK hxy]
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have key : ((c.monoC x * c.monoC y)⁻¹ * c.monoC (x.mul y) : GL (Fin 6) K) =
      (c.scalGL (x.raw y 0))⁻¹ := by
    rw [monoC_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hmem : (c.scalGL (x.raw y 0))⁻¹ ∈ StatedScalars (Fin 6) K :=
    Subgroup.inv_mem _ ⟨_, rfl⟩
  change ((c.monoC x * c.monoC y)⁻¹ * c.monoC (x.mul y) : GL (Fin 6) K) ∈ _
  rw [key]
  exact hmem

theorem mu_one : c.mu hK U6Mon.one = 1 := by
  rw [mu_of_ok c hK U6Mon.ok_one]
  have : (⟨c.monoC U6Mon.one, c.monoC_mem hK U6Mon.ok_one⟩ : StatedSU 6 (2 ^ 1) K) = 1 :=
    Subtype.ext (c.monoC_one)
  rw [this]
  exact QuotientGroup.mk_one _

theorem mu_injective {x y : U6Mon} (hx : x.Ok) (hy : y.Ok) (h : c.mu hK x = c.mu hK y) :
    x = y := by
  rw [mu_of_ok c hK hx, mu_of_ok c hK hy] at h
  have h1 := QuotientGroup.eq.1 h
  rw [Subgroup.mem_subgroupOf] at h1
  obtain ⟨u, hu⟩ := h1
  have h2 : c.monoC y = c.monoC x * Matrix.GeneralLinearGroup.scalar (Fin 6) u := by
    have : (c.monoC x)⁻¹ * c.monoC y = Matrix.GeneralLinearGroup.scalar (Fin 6) u := by
      simpa using hu.symm
    rw [← this, mul_inv_cancel_left]
  have h3 : c.mono y.d (u6Perm y.t) = (u : K) • c.mono x.d (u6Perm x.t) := by
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) h2
    simp only [monoC, monoGL_val, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [this, mono_mul_scalar]
  obtain ⟨hσ, hd⟩ := c.mono_eq_smul h3
  have ht : y.t = x.t := u6Perm_injective hσ
  have hu1 : (u : K) = 1 := by
    have := hd 0
    rw [hx.1, hy.1, c.p_zero, mul_one] at this
    exact this.symm
  refine U6Mon.ext' (funext fun i => c.p_injective ?_).symm ht.symm
  rw [hd i, hu1, one_mul]

theorem mu_foldl {w : List U6Mon} (hw : ∀ g ∈ w, g.Ok) {a : U6Mon} (ha : a.Ok) :
    c.mu hK (w.foldl U6Mon.mul a) = c.mu hK a * (w.map (c.mu hK)).prod := by
  induction w generalizing a with
  | nil => simp
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    rw [List.foldl_cons, ih (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')) (U6Mon.ok_mul ha hg),
      ← mu_mul c hK ha hg, List.map_cons, List.prod_cons, mul_assoc]

theorem mu_evalWord (w : List ℕ) :
    c.mu hK (U6Mon.evalWord w) = (w.map fun k => c.mu hK (U6Mon.gen k)).prod := by
  unfold U6Mon.evalWord
  rw [mu_foldl c hK (fun g hg => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    exact U6Mon.ok_gen k) U6Mon.ok_one, mu_one, one_mul, List.map_map]
  rfl

end Mu

end Cube

end CFSG.RankThree.PartOne.F106
