module

public import CFSG.Monster.Griess.Axis
public import CFSG.Monster.Griess.ShortPairs
public import CFSG.Monster.Griess.TrilinearData
public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix Module

variable {r : Q}

noncomputable abbrev shortCls (hr : IsShortCoord (coordOf r)) : ShortIdx := ⟨coordOf r, hr⟩

theorem uQ_eq_ratVec (c : ShortIdx) : uQ c = ratVec (uvec c) := rfl

theorem uQ_dotProduct_uQ_self (c : ShortIdx) : uQ c ⬝ᵥ uQ c = 32 :=
  ratVec_dotProduct_self (uvec_mem c)

theorem axisE_coe (hr : IsShortCoord (coordOf r)) :
    (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = (32 : ℚ)⁻¹ • vecMulVec (uQ (shortCls hr))
      (uQ (shortCls hr)) := by
  rw [coe_axisE hr]
  rfl

theorem Umat_eq_axisE (hr : IsShortCoord (coordOf r)) :
    Umat (shortCls hr) = (32 : ℚ) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ) := by
  rw [axisE_coe hr, smul_smul]
  norm_num
  rfl

theorem trace_axisE (hr : IsShortCoord (coordOf r)) :
    trace (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = 1 := by
  rw [coe_axisE hr]
  exact trace_projMat (uvec_mem _)

theorem axisE_mul_self (hr : IsShortCoord (coordOf r)) :
    (axisE r : Matrix (Fin 24) (Fin 24) ℚ) * (axisE r : Matrix (Fin 24) (Fin 24) ℚ) =
      (axisE r : Matrix (Fin 24) (Fin 24) ℚ) := by
  rw [coe_axisE hr]
  exact projMat_mul_self (uvec_mem _)

theorem qf_axisE (hr : IsShortCoord (coordOf r)) (d : ShortIdx) :
    qf d (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = (uQ d ⬝ᵥ uQ (shortCls hr)) ^ 2 / 32 := by
  rw [axisE_coe hr, qf_smul, qf_vecMulVec, dotProduct_comm (uQ (shortCls hr)) (uQ d)]
  ring

theorem Am_axis (r : Q) : Am (axis r) = (2 : ℚ) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ) := by
  simp [axis, Am]

theorem xs_axis (r : Q) : xs (axis r) = -((2 : ℚ) • Xlift r) := by
  simp [axis, xs]

theorem Nm_axis (r : Q) : Nm (axis r) = 0 := by
  simp [axis, Nm]

theorem xs_axis_apply (hr : IsShortCoord (coordOf r)) (d : ShortIdx) :
    xs (axis r) d = if d = shortCls hr then -(2 * sgn (centralCoord r)) else 0 := by
  rw [xs_axis, Xlift_eq hr]
  simp only [Pi.neg_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem axisMul_A (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    ((gmul (axis r) v).1 : Matrix (Fin 24) (Fin 24) ℚ) =
      (4 : ℚ) • ((axisE r : Matrix (Fin 24) (Fin 24) ℚ) * Am v +
        Am v * (axisE r : Matrix (Fin 24) (Fin 24) ℚ)) -
      (8 * sgn (centralCoord r) * xs v (shortCls hr)) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ) := by
  have hsum : ∑ c, (xs (axis r) c * xs v c) • Umat c =
      (-(2 * sgn (centralCoord r)) * xs v (shortCls hr)) • Umat (shortCls hr) := by
    rw [Finset.sum_eq_single (shortCls hr)]
    · rw [xs_axis_apply hr, ite_eq_left rfl]
    · intro d _ hd
      rw [xs_axis_apply hr, ite_eq_right hd, zero_mul, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  change gmulA (axis r) v = _
  rw [gmulA, hsum, Nm_axis, Am_axis, Umat_eq_axisE hr]
  simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, trace_zero, zero_div, zero_smul,
    add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  module

theorem axisMul_X (hr : IsShortCoord (coordOf r)) (v : SpaceB) (d : ShortIdx) :
    (gmul (axis r) v).2.1 d =
      xs v d * (uQ d ⬝ᵥ uQ (shortCls hr)) ^ 2 / 128 -
        (if d = shortCls hr then sgn (centralCoord r) * qf d (Am v) / 4 else 0) -
        2 * sgn (centralCoord r) * ∑ f, xs v f * tau (shortCls hr) f d := by
  have hsum : ∑ e, ∑ f, xs (axis r) e * xs v f * tau e f d =
      -(2 * sgn (centralCoord r)) * ∑ f, xs v f * tau (shortCls hr) f d := by
    rw [Finset.sum_eq_single (shortCls hr)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [xs_axis_apply hr, ite_eq_left rfl]
      ring
    · intro e _ he
      refine Finset.sum_eq_zero fun f _ => ?_
      rw [xs_axis_apply hr, ite_eq_right he, zero_mul, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  change gmulX (axis r) v d = _
  rw [gmulX, hsum, Nm_axis, Am_axis, qf_smul, qf_axisE hr, xs_axis_apply hr]
  simp only [transpose_zero, Matrix.zero_mul, trace_zero, qf_zero, zero_div, sub_zero, add_zero]
  split_ifs with h
  · subst h
    ring
  · ring

theorem axisMul_W (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    (gmul (axis r) v).2.2 =
      (4 : ℚ)⁻¹ • Nm v + (2 : ℚ) • (Nm v * (axisE r : Matrix (Fin 24) (Fin 24) ℚ)) -
        (sgn (centralCoord r) / 4) • (Rmat (shortCls hr) * Nm v -
          (8 : ℚ) • (Rmat (shortCls hr) * Nm v * (axisE r : Matrix (Fin 24) (Fin 24) ℚ))) := by
  have h1 : gmulWHalf v (axis r) = 0 := by
    simp [gmulWHalf, Nm_axis]
  have hsum : ∑ c, xs (axis r) c • (Rmat c * Nm v - (4 : ℚ)⁻¹ • (Rmat c * Nm v * Umat c)) =
      (-(2 * sgn (centralCoord r))) • (Rmat (shortCls hr) * Nm v -
        (4 : ℚ)⁻¹ • (Rmat (shortCls hr) * Nm v * Umat (shortCls hr))) := by
    rw [Finset.sum_eq_single (shortCls hr)]
    · rw [xs_axis_apply hr, ite_eq_left rfl]
    · intro d _ hd
      rw [xs_axis_apply hr, ite_eq_right hd, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  change gmulWHalf (axis r) v + gmulWHalf v (axis r) = _
  rw [h1, add_zero, gmulWHalf, hsum, Am_axis, trace_smul, trace_axisE hr, Umat_eq_axisE hr]
  simp only [Matrix.mul_smul, smul_smul, smul_eq_mul]
  module

theorem classOf_ne_zero_of_mem_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : classOf u ≠ 0 := by
  intro h
  simp only [classOf, dite_eq_left hu.1] at h
  rw [Submodule.Quotient.mk_eq_zero, mem_two_range_iff] at h
  obtain ⟨w, hw⟩ := h
  have hw' : (2 : ℤ) • (w : Fin 24 → ℤ) = u := hw
  have hw0 : (w : Fin 24 → ℤ) ≠ 0 := fun h0 => minVecs_ne_zero hu (by rw [← hw', h0, smul_zero])
  have h32 := normSq_ge w.2 hw0
  have hu32 := (mem_minVecs_iff.1 hu).2
  rw [← hw', normSq_two_smul] at hu32
  omega

theorem not_isShortCoord_zero : ¬ IsShortCoord 0 := by
  rintro ⟨u, hu, h⟩
  rw [map_zero] at h
  exact classOf_ne_zero_of_mem_minVecs hu h

theorem tau_self_left (c d : ShortIdx) : tau c c d = 0 := by
  unfold tau
  rw [ite_eq_right]
  intro h
  rw [add_self_coord] at h
  exact not_isShortCoord_zero (h ▸ d.2)

theorem sum_xs_axis_tau (hr : IsShortCoord (coordOf r)) (d : ShortIdx) :
    ∑ f, xs (axis r) f * tau (shortCls hr) f d = 0 := by
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [xs_axis_apply hr]
  split_ifs with h
  · rw [h, tau_self_left, mul_zero]
  · rw [zero_mul]

theorem sgn_sq (t : ZMod 2) : sgn t * sgn t = 1 := sgn_mul_self t

theorem axis_mul_self (hr : IsShortCoord (coordOf r)) :
    gmul (axis r) (axis r) = (16 : ℚ) • axis r := by
  have hσ := sgn_sq (centralCoord r)
  have hE := axisE_mul_self hr
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun d => ?_) ?_)
  · rw [axisMul_A hr, xs_axis_apply hr, ite_eq_left rfl]
    change _ = (16 : ℚ) • Am (axis r)
    rw [Am_axis]
    simp only [Matrix.smul_mul, Matrix.mul_smul, hE]
    have : 8 * sgn (centralCoord r) * -(2 * sgn (centralCoord r)) = -16 := by
      linear_combination (-16) * hσ
    rw [this]
    module
  · rw [axisMul_X hr, sum_xs_axis_tau hr, mul_zero, sub_zero]
    change _ = (16 : ℚ) * xs (axis r) d
    rw [xs_axis_apply hr]
    split_ifs with h
    · subst h
      rw [Am_axis, qf_smul, qf_axisE hr, uQ_dotProduct_uQ_self]
      linear_combination (-16 * sgn (centralCoord r)) * hσ + 16 * sgn (centralCoord r) * hσ
    · ring
  · rw [axisMul_W hr, Nm_axis]
    change _ = (16 : ℚ) • Nm (axis r)
    simp [Nm_axis]

theorem bform_axis_self (hr : IsShortCoord (coordOf r)) : bform (axis r) (axis r) = 8 := by
  have hσ := sgn_sq (centralCoord r)
  rw [bform_apply]
  change trace (Am (axis r) * Am (axis r)) + ∑ c, xs (axis r) c * xs (axis r) c +
    ∑ j, ∑ i, Nm (axis r) j i * Nm (axis r) j i = 8
  rw [Am_axis, Nm_axis, Matrix.smul_mul, Matrix.mul_smul, axisE_mul_self hr, trace_smul,
    trace_smul, trace_axisE hr]
  have hs : ∑ c, xs (axis r) c * xs (axis r) c = 4 := by
    rw [Finset.sum_eq_single (shortCls hr)]
    · rw [xs_axis_apply hr, ite_eq_left rfl]
      linear_combination 4 * hσ
    · intro d _ hd
      rw [xs_axis_apply hr, ite_eq_right hd, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hs]
  simp
  norm_num

theorem uQ_dotProduct_uQ (c d : ShortIdx) : uQ c ⬝ᵥ uQ d = 8 * (alphaS c d : ℚ) := by
  have h := eight_mul_alphaS c d
  rw [uQ_eq_ratVec, uQ_eq_ratVec, dotProduct]
  simp only [ratVec]
  exact_mod_cast h.symm

@[expose] noncomputable def betaX (c d : ShortIdx) : ℚ := (uQ d ⬝ᵥ uQ c) ^ 2 / 128

theorem betaX_eq (c d : ShortIdx) : betaX c d = (alphaS d c : ℚ) ^ 2 / 2 := by
  rw [betaX, uQ_dotProduct_uQ]
  ring

@[expose] noncomputable def Kop (σ : ℚ) (c : ShortIdx) : SpaceX →ₗ[ℚ] SpaceX where
  toFun x d := x d * betaX c d - 2 * σ * ∑ f, x f * tau c f d
  map_add' x y := by
    funext d
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' t x := by
    funext d
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]
    ring

theorem Kop_apply (σ : ℚ) (c : ShortIdx) (x : SpaceX) (d : ShortIdx) :
    Kop σ c x d = x d * betaX c d - 2 * σ * ∑ f, x f * tau c f d := rfl

theorem sum_single_mul_tau (c d e : ShortIdx) :
    ∑ f, (Pi.single d 1 : SpaceX) f * tau c f e = tau c d e := by
  rw [Finset.sum_eq_single d]
  · simp
  · intro f _ hf
    simp [hf]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tau_eq_zero_of_not_short {c d : ShortIdx} (h : ¬ IsShortCoord (c.1 + d.1)) (e : ShortIdx) :
    tau c d e = 0 := by
  unfold tau
  rw [ite_eq_right]
  intro he
  exact h (he ▸ e.2)

theorem Kop_single_of_not_short (σ : ℚ) {c d : ShortIdx} (h : ¬ IsShortCoord (c.1 + d.1)) :
    Kop σ c (Pi.single d 1) = betaX c d • Pi.single d 1 := by
  funext e
  rw [Kop_apply, sum_single_mul_tau, tau_eq_zero_of_not_short h, mul_zero, sub_zero]
  by_cases he : e = d
  · subst he
    simp
  · simp [he]

theorem tau_of_eq_add {c d e : ShortIdx} (he : e.1 = c.1 + d.1) (e' : ShortIdx) :
    tau c d e' = if e' = e then sgn (pair d.1.1 c.1.2) else 0 := by
  unfold tau
  by_cases h' : e' = e
  · rw [ite_eq_left (by rw [h', he]), ite_eq_left h']
  · rw [ite_eq_right (fun h'' => h' (Subtype.ext (h''.trans he.symm))), ite_eq_right h']

theorem ne_of_eq_add {c d e : ShortIdx} (he : e.1 = c.1 + d.1) : d ≠ e := fun hde =>
  not_isShortCoord_zero (by
    have h1 : d.1 = c.1 + d.1 := (congrArg Subtype.val hde).trans he
    have h2 : c.1 = 0 := by
      have := congrArg (· + d.1) h1
      simp only [add_assoc, add_self_coord, add_zero] at this
      exact this.symm
    exact h2 ▸ c.2)

theorem Kop_single_of_eq_add (σ : ℚ) {c d e : ShortIdx} (he : e.1 = c.1 + d.1) :
    Kop σ c (Pi.single d 1) = betaX c d • Pi.single d 1 -
      (2 * σ * sgn (pair d.1.1 c.1.2)) • Pi.single e 1 := by
  have hde := ne_of_eq_add he
  funext e'
  rw [Kop_apply, sum_single_mul_tau, tau_of_eq_add he]
  by_cases h1 : e' = d
  · subst h1
    simp [hde]
  · by_cases h2 : e' = e
    · subst h2
      simp [h1]
    · simp [h1, h2]

@[expose] noncomputable def cubicQ {M : Type*} [AddCommGroup M] [Module ℚ M] (f : M →ₗ[ℚ] M) :
    M →ₗ[ℚ] M :=
  f ∘ₗ f ∘ₗ f - (9 / 2 : ℚ) • (f ∘ₗ f) + (2 : ℚ) • f

theorem cubicQ_apply {M : Type*} [AddCommGroup M] [Module ℚ M] (f : M →ₗ[ℚ] M) (x : M) :
    cubicQ f x = f (f (f x)) - (9 / 2 : ℚ) • f (f x) + (2 : ℚ) • f x := rfl

theorem cubicQ_of_eigen {M : Type*} [AddCommGroup M] [Module ℚ M] (f : M →ₗ[ℚ] M) {x : M}
    {β : ℚ} (hx : f x = β • x) (hβ : β = 0 ∨ β = 4 ∨ β = 1 / 2) : cubicQ f x = 0 := by
  have h : cubicQ f x = (β * β * β - 9 / 2 * (β * β) + 2 * β) • x := by
    rw [cubicQ_apply, hx, map_smul, hx, map_smul, map_smul, hx]
    module
  rw [h]
  rcases hβ with rfl | rfl | rfl <;> norm_num

theorem cubicQ_of_sq {M : Type*} [AddCommGroup M] [Module ℚ M] (f : M →ₗ[ℚ] M) {x : M}
    (hx : f (f x) = (4 : ℚ) • f x) : cubicQ f x = 0 := by
  rw [cubicQ_apply, hx, map_smul, hx]
  module

theorem add_add_cancel_coord (c d : C × Cocode) : c + (c + d) = d := by
  rw [← add_assoc, add_self_coord, zero_add]

theorem cubicQ_Kop_single {σ : ℚ} (hσ : σ * σ = 1) {c d : ShortIdx} (hcd : d ≠ c) :
    cubicQ (Kop σ c) (Pi.single d 1) = 0 := by
  by_cases h : IsShortCoord (c.1 + d.1)
  ·
    obtain ⟨e, he⟩ : ∃ e : ShortIdx, e.1 = c.1 + d.1 := ⟨⟨_, h⟩, rfl⟩
    have he' : d.1 = c.1 + e.1 := by rw [he, add_add_cancel_coord]
    have hα : alphaS d c ^ 2 = 4 := by
      rcases (isShortCoord_add_iff (Ne.symm hcd)).1 h with h2 | h2 <;>
        rw [alphaS_comm, h2] <;> norm_num
    have hα' : alphaS e c ^ 2 = 4 := by
      have := alphaS_add_sq (Ne.symm hcd) h
      have hee : (⟨c.1 + d.1, h⟩ : ShortIdx) = e := Subtype.ext he.symm
      rw [hee] at this
      rw [alphaS_comm]
      exact this
    have hβ : betaX c d = 2 := by
      rw [betaX_eq]
      have : ((alphaS d c : ℤ) : ℚ) ^ 2 = 4 := by exact_mod_cast hα
      rw [this]
      norm_num
    have hβ' : betaX c e = 2 := by
      rw [betaX_eq]
      have : ((alphaS e c : ℤ) : ℚ) ^ 2 = 4 := by exact_mod_cast hα'
      rw [this]
      norm_num
    have hpe : pair e.1.1 c.1.2 = pair d.1.1 c.1.2 := by
      rw [he, Prod.fst_add, pair_add_left, pair_eq_zero_of_isShortCoord c.2, zero_add]
    have hss : (2 * σ * sgn (pair d.1.1 c.1.2)) * (2 * σ * sgn (pair d.1.1 c.1.2)) = 4 := by
      have := sgn_sq (pair d.1.1 c.1.2)
      linear_combination 4 * sgn (pair d.1.1 c.1.2) ^ 2 * hσ + 4 * this
    have k1 := Kop_single_of_eq_add σ he
    have k2 := Kop_single_of_eq_add σ he'
    rw [hβ] at k1
    rw [hβ', hpe] at k2
    apply cubicQ_of_sq
    rw [k1, map_sub, map_smul, map_smul, k1, k2]
    generalize 2 * σ * sgn (pair d.1.1 c.1.2) = s at hss ⊢
    have e2 : (2 : ℚ) • ((2 : ℚ) • Pi.single d 1 - s • Pi.single e 1) -
        s • ((2 : ℚ) • Pi.single e 1 - s • Pi.single d 1) =
        (4 + s * s) • (Pi.single d 1 : SpaceX) - (4 * s) • Pi.single e 1 := by
      module
    rw [e2, hss]
    module
  · apply cubicQ_of_eigen _ (Kop_single_of_not_short σ h)
    rw [betaX_eq]
    rcases alphaS_mem (Ne.symm hcd) with h2 | h2 | h2 | h2 | h2
    · exact absurd ((isShortCoord_add_iff (Ne.symm hcd)).2 (Or.inr h2)) h
    · rw [alphaS_comm, h2]; norm_num
    · rw [alphaS_comm, h2]; norm_num
    · rw [alphaS_comm, h2]; norm_num
    · exact absurd ((isShortCoord_add_iff (Ne.symm hcd)).2 (Or.inl h2)) h

theorem cubicQ_Kop {σ : ℚ} (hσ : σ * σ = 1) {c : ShortIdx} {x : SpaceX} (hx : x c = 0) :
    cubicQ (Kop σ c) x = 0 := by
  have hdec : x = ∑ d, x d • (Pi.single d 1 : SpaceX) := by
    funext e
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hdec, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [map_smul]
  by_cases hd : d = c
  · rw [hd, hx, zero_smul]
  · rw [cubicQ_Kop_single hσ hd, smul_zero]

theorem axisE_mul_mul_axisE (hr : IsShortCoord (coordOf r)) (A : Matrix (Fin 24) (Fin 24) ℚ) :
    (axisE r : Matrix (Fin 24) (Fin 24) ℚ) * A * (axisE r : Matrix (Fin 24) (Fin 24) ℚ) =
      (qf (shortCls hr) A / 32) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ) := by
  rw [axisE_coe hr, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul,
    vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul, smul_smul, qf,
    dotProduct_mulVec]
  congr 1
  ring

@[expose] noncomputable def MAop (E : Matrix (Fin 24) (Fin 24) ℚ) :
    Matrix (Fin 24) (Fin 24) ℚ →ₗ[ℚ] Matrix (Fin 24) (Fin 24) ℚ where
  toFun A := (4 : ℚ) • (E * A + A * E)
  map_add' A B := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' t A := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
    module

theorem MAop_apply (E A : Matrix (Fin 24) (Fin 24) ℚ) : MAop E A = (4 : ℚ) • (E * A + A * E) := rfl

theorem MAop_MAop (hr : IsShortCoord (coordOf r)) {A : Matrix (Fin 24) (Fin 24) ℚ}
    (hA : qf (shortCls hr) A = 0) :
    MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) A) =
      (4 : ℚ) • MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) A := by
  have hE := axisE_mul_self hr
  have hEAE := axisE_mul_mul_axisE hr A
  rw [hA, zero_div, zero_smul] at hEAE
  simp only [MAop_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_assoc, hE, hEAE]
  rw [Matrix.mul_assoc A, hE]
  module

@[expose] noncomputable def LWop (σ : ℚ) (R : Matrix SpinIdx SpinIdx ℚ)
    (E : Matrix (Fin 24) (Fin 24) ℚ) : SpaceW →ₗ[ℚ] SpaceW where
  toFun N := (4 : ℚ)⁻¹ • N + (2 : ℚ) • (N * E) - (σ / 4) • (R * N - (8 : ℚ) • (R * N * E))
  map_add' N M := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' t N := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
    module

theorem LWop_apply (σ : ℚ) (R : Matrix SpinIdx SpinIdx ℚ) (E : Matrix (Fin 24) (Fin 24) ℚ)
    (N : SpaceW) : LWop σ R E N =
      (4 : ℚ)⁻¹ • N + (2 : ℚ) • (N * E) - (σ / 4) • (R * N - (8 : ℚ) • (R * N * E)) := rfl

theorem cubicQ_LWop {σ : ℚ} (hσ : σ = 1 ∨ σ = -1) {R : Matrix SpinIdx SpinIdx ℚ}
    (hR : R * R = 1) {E : Matrix (Fin 24) (Fin 24) ℚ} (hE : E * E = E) (N : SpaceW) :
    cubicQ (LWop σ R E) N = 0 := by
  have hRR : ∀ M : SpaceW, R * (R * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hR, Matrix.one_mul]
  have hEE : ∀ M : SpaceW, M * E * E = M * E := fun M => by rw [Matrix.mul_assoc, hE]
  have a1 : LWop σ R E N = (4 : ℚ)⁻¹ • N + (2 : ℚ) • (N * E) - (σ / 4) • (R * N) +
      (2 * σ) • (R * N * E) := by
    rw [LWop_apply]
    module
  have a2 : LWop σ R E (N * E) = (9 / 4 : ℚ) • (N * E) + (7 * σ / 4) • (R * N * E) := by
    rw [LWop_apply, hEE, ← Matrix.mul_assoc R N E, Matrix.mul_assoc (R * N) E E, hE]
    module
  have a3 : LWop σ R E (R * N) = -(σ / 4) • N + (2 * σ) • (N * E) + (4 : ℚ)⁻¹ • (R * N) +
      (2 : ℚ) • (R * N * E) := by
    rw [LWop_apply, hRR]
    module
  have a4 : LWop σ R E (R * N * E) = (7 * σ / 4) • (N * E) + (9 / 4 : ℚ) • (R * N * E) := by
    rw [LWop_apply, hEE, Matrix.mul_assoc R N E, hRR, hEE]
    module
  rw [cubicQ_apply]
  simp only [map_add, map_sub, map_smul, a1, a2, a3, a4]
  rcases hσ with rfl | rfl <;> module

theorem Rmat_mul_self (c : ShortIdx) : Rmat c * Rmat c = 1 := by
  rw [Rmat, qmatR_mul, add_self_coord' c.1.1, add_self_cocode', pair_eq_zero_of_isShortCoord c.2,
    add_zero, add_zero, qmatR_zero]
where
  add_self_coord' (a : C) : a + a = 0 := by
    rw [← two_smul (ZMod 2) a, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  add_self_cocode' (δ : Cocode) : δ + δ = 0 := by
    rw [← two_smul (ZMod 2) δ, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem tau_self_right (c f : ShortIdx) : tau c f c = 0 := by
  unfold tau
  rw [ite_eq_right]
  intro h
  have h' : f.1 = 0 := by
    have := congrArg (c.1 + ·) h
    simp only [← add_assoc, add_self_coord, zero_add] at this
    exact this.symm
  exact not_isShortCoord_zero (h' ▸ f.2)

@[expose] def IsPerpAx (hr : IsShortCoord (coordOf r)) (v : SpaceB) : Prop :=
  qf (shortCls hr) (Am v) = 0 ∧ xs v (shortCls hr) = 0

theorem axisMul_A_perp (hr : IsShortCoord (coordOf r)) {v : SpaceB} (hv : IsPerpAx hr v) :
    ((gmul (axis r) v).1 : Matrix (Fin 24) (Fin 24) ℚ) =
      MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Am v) := by
  rw [axisMul_A hr, hv.2, mul_zero, zero_smul, sub_zero, MAop_apply]

theorem axisMul_X_perp (hr : IsShortCoord (coordOf r)) {v : SpaceB} (hv : IsPerpAx hr v) :
    (gmul (axis r) v).2.1 = Kop (sgn (centralCoord r)) (shortCls hr) (xs v) := by
  funext d
  rw [axisMul_X hr, Kop_apply, betaX]
  split_ifs with h
  · subst h
    rw [hv.1, mul_zero, zero_div, sub_zero]
    ring
  · rw [sub_zero]
    ring

theorem axisMul_W' (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    (gmul (axis r) v).2.2 = LWop (sgn (centralCoord r)) (Rmat (shortCls hr))
      (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Nm v) := by
  rw [axisMul_W hr, LWop_apply]

theorem qf_MAop (hr : IsShortCoord (coordOf r)) (A : Matrix (Fin 24) (Fin 24) ℚ) :
    qf (shortCls hr) (MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) A) = 8 * qf (shortCls hr) A := by
  have hu : uQ (shortCls hr) ᵥ* (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = uQ (shortCls hr) := by
    rw [coe_axisE hr]
    exact vecMul_projMat_self (uvec_mem _)
  have hu' : (axisE r : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ uQ (shortCls hr) = uQ (shortCls hr) := by
    rw [← vecMul_transpose, show (axisE r : Matrix (Fin 24) (Fin 24) ℚ)ᵀ = axisE r from (axisE r).2,
      hu]
  rw [MAop_apply, qf_smul]
  unfold qf
  rw [Matrix.add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, hu', dotProduct_mulVec,
    hu]
  ring

theorem isPerpAx_gmul (hr : IsShortCoord (coordOf r)) {v : SpaceB} (hv : IsPerpAx hr v) :
    IsPerpAx hr (gmul (axis r) v) := by
  refine ⟨?_, ?_⟩
  · change qf (shortCls hr) ((gmul (axis r) v).1 : Matrix (Fin 24) (Fin 24) ℚ) = 0
    rw [axisMul_A_perp hr hv, qf_MAop hr, hv.1, mul_zero]
  · change (gmul (axis r) v).2.1 (shortCls hr) = 0
    rw [axisMul_X_perp hr hv, Kop_apply, hv.2, zero_mul, zero_sub, neg_eq_zero]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun f _ => ?_)
    rw [tau_self_right, mul_zero]

theorem sgn_eq_one_or (t : ZMod 2) : sgn t = 1 ∨ sgn t = -1 := by
  unfold sgn
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem cubicQ_axis_perp (hr : IsShortCoord (coordOf r)) {v : SpaceB} (hv : IsPerpAx hr v) :
    cubicQ (gmul (axis r)) v = 0 := by
  have hv1 := isPerpAx_gmul hr hv
  have hv2 := isPerpAx_gmul hr hv1
  have hσ := sgn_sq (centralCoord r)
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · change ((cubicQ (gmul (axis r)) v).1 : Matrix (Fin 24) (Fin 24) ℚ) = 0
    rw [cubicQ_apply]
    simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_smul]
    rw [axisMul_A_perp hr hv2, axisMul_A_perp hr hv1, axisMul_A_perp hr hv]
    have h1 : Am (gmul (axis r) v) = MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Am v) :=
      axisMul_A_perp hr hv
    have h2 : Am (gmul (axis r) (gmul (axis r) v)) =
        MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ)
          (Am v)) := by
      rw [show Am (gmul (axis r) (gmul (axis r) v)) =
        ((gmul (axis r) (gmul (axis r) v)).1 : Matrix (Fin 24) (Fin 24) ℚ) from rfl,
        axisMul_A_perp hr hv1, h1]
    rw [h2, h1]
    have := cubicQ_of_sq (MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ)) (MAop_MAop hr hv.1)
    rw [cubicQ_apply] at this
    exact this
  · change (cubicQ (gmul (axis r)) v).2.1 = 0
    rw [cubicQ_apply]
    simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, Prod.fst_add, Prod.fst_sub,
      Prod.smul_fst]
    rw [axisMul_X_perp hr hv2, axisMul_X_perp hr hv1, axisMul_X_perp hr hv]
    have h1 : xs (gmul (axis r) v) = Kop (sgn (centralCoord r)) (shortCls hr) (xs v) :=
      axisMul_X_perp hr hv
    have h2 : xs (gmul (axis r) (gmul (axis r) v)) = Kop (sgn (centralCoord r)) (shortCls hr)
        (Kop (sgn (centralCoord r)) (shortCls hr) (xs v)) := by
      rw [show xs (gmul (axis r) (gmul (axis r) v)) = (gmul (axis r) (gmul (axis r) v)).2.1 from rfl,
        axisMul_X_perp hr hv1, h1]
    rw [h2, h1]
    have := cubicQ_Kop hσ hv.2
    rw [cubicQ_apply] at this
    exact this
  · change (cubicQ (gmul (axis r)) v).2.2 = 0
    rw [cubicQ_apply]
    simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd]
    rw [axisMul_W' hr, axisMul_W' hr, axisMul_W' hr]
    have h1 : Nm (gmul (axis r) v) = LWop (sgn (centralCoord r)) (Rmat (shortCls hr))
        (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Nm v) := axisMul_W' hr v
    have h2 : Nm (gmul (axis r) (gmul (axis r) v)) = LWop (sgn (centralCoord r))
        (Rmat (shortCls hr)) (axisE r : Matrix (Fin 24) (Fin 24) ℚ)
        (LWop (sgn (centralCoord r)) (Rmat (shortCls hr)) (axisE r : Matrix (Fin 24) (Fin 24) ℚ)
          (Nm v)) := by
      rw [show Nm (gmul (axis r) (gmul (axis r) v)) = (gmul (axis r) (gmul (axis r) v)).2.2 from rfl,
        axisMul_W' hr, h1]
    rw [h2, h1]
    have := cubicQ_LWop (sgn_eq_one_or (centralCoord r)) (Rmat_mul_self (shortCls hr))
      (axisE_mul_self hr) (Nm v)
    rw [cubicQ_apply] at this
    exact this

theorem Am_axis_zQ (hr : IsShortCoord (coordOf r)) :
    Am (axis (zQ * r)) = (2 : ℚ) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ) := by
  rw [axis_zQ_mul hr]
  simp [Am]

theorem Nm_axis_zQ (hr : IsShortCoord (coordOf r)) : Nm (axis (zQ * r)) = 0 := by
  rw [axis_zQ_mul hr]
  simp [Nm]

theorem xs_axis_zQ_apply (hr : IsShortCoord (coordOf r)) (d : ShortIdx) :
    xs (axis (zQ * r)) d = if d = shortCls hr then 2 * sgn (centralCoord r) else 0 := by
  rw [axis_zQ_mul hr]
  simp only [xs, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Pi.add_apply,
    Pi.smul_apply, smul_zero, Pi.zero_apply, zero_add, Xlift_eq hr, Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem axis_mul_axis_zQ (hr : IsShortCoord (coordOf r)) : gmul (axis r) (axis (zQ * r)) = 0 := by
  have hσ := sgn_sq (centralCoord r)
  have hE := axisE_mul_self hr
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun d => ?_) ?_)
  · rw [axisMul_A hr, xs_axis_zQ_apply hr, ite_eq_left rfl, Am_axis_zQ hr]
    simp only [Matrix.smul_mul, Matrix.mul_smul, hE]
    change _ = (0 : Matrix (Fin 24) (Fin 24) ℚ)
    have : 8 * sgn (centralCoord r) * (2 * sgn (centralCoord r)) = 16 := by
      linear_combination 16 * hσ
    rw [this]
    module
  · rw [axisMul_X hr]
    have hsum : ∑ f, xs (axis (zQ * r)) f * tau (shortCls hr) f d = 0 := by
      refine Finset.sum_eq_zero fun f _ => ?_
      rw [xs_axis_zQ_apply hr]
      split_ifs with h
      · rw [h, tau_self_left, mul_zero]
      · rw [zero_mul]
    rw [hsum, mul_zero, sub_zero, xs_axis_zQ_apply hr]
    change _ = (0 : ℚ)
    split_ifs with h
    · subst h
      rw [Am_axis_zQ hr, qf_smul, qf_axisE hr, uQ_dotProduct_uQ_self]
      linear_combination 0 * hσ
    · ring
  · rw [axisMul_W hr, Nm_axis_zQ hr]
    simp

theorem bform_axis_axis_zQ (hr : IsShortCoord (coordOf r)) :
    bform (axis (zQ * r)) (axis (zQ * r)) = 8 := by
  have h := bform_axis_self (isShortCoord_zQ_mul hr)
  exact h

theorem trace_mul_axisE (hr : IsShortCoord (coordOf r)) (A : Matrix (Fin 24) (Fin 24) ℚ) :
    trace (A * (axisE r : Matrix (Fin 24) (Fin 24) ℚ)) = qf (shortCls hr) A / 32 := by
  rw [trace_mul_comm, axisE_coe hr, Matrix.smul_mul, trace_smul, smul_eq_mul]
  have : trace (vecMulVec (uQ (shortCls hr)) (uQ (shortCls hr)) * A) = qf (shortCls hr) A :=
    trace_Umat_mul (shortCls hr) A
  rw [this]
  ring

theorem bform_axis_left (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    bform v (axis r) = qf (shortCls hr) (Am v) / 16 - 2 * sgn (centralCoord r) * xs v (shortCls hr) := by
  rw [bform_apply]
  change trace (Am v * Am (axis r)) + ∑ c, xs v c * xs (axis r) c +
    ∑ j, ∑ i, Nm v j i * Nm (axis r) j i = _
  rw [Am_axis, Nm_axis, Matrix.mul_smul, trace_smul, trace_mul_axisE hr, smul_eq_mul]
  have hs : ∑ c, xs v c * xs (axis r) c = -(2 * sgn (centralCoord r)) * xs v (shortCls hr) := by
    rw [Finset.sum_eq_single (shortCls hr)]
    · rw [xs_axis_apply hr, ite_eq_left rfl]
      ring
    · intro d _ hd
      rw [xs_axis_apply hr, ite_eq_right hd, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hs]
  simp
  ring

theorem bform_axis_zQ_left (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    bform v (axis (zQ * r)) =
      qf (shortCls hr) (Am v) / 16 + 2 * sgn (centralCoord r) * xs v (shortCls hr) := by
  rw [bform_apply]
  change trace (Am v * Am (axis (zQ * r))) + ∑ c, xs v c * xs (axis (zQ * r)) c +
    ∑ j, ∑ i, Nm v j i * Nm (axis (zQ * r)) j i = _
  rw [Am_axis_zQ hr, Nm_axis_zQ hr, Matrix.mul_smul, trace_smul, trace_mul_axisE hr, smul_eq_mul]
  have hs : ∑ c, xs v c * xs (axis (zQ * r)) c = 2 * sgn (centralCoord r) * xs v (shortCls hr) := by
    rw [Finset.sum_eq_single (shortCls hr)]
    · rw [xs_axis_zQ_apply hr, ite_eq_left rfl]
      ring
    · intro d _ hd
      rw [xs_axis_zQ_apply hr, ite_eq_right hd, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hs]
  simp
  ring

@[expose] noncomputable def perpPart (r : Q) (v : SpaceB) : SpaceB :=
  v - (bform v (axis r) / 8) • axis r - (bform v (axis (zQ * r)) / 8) • axis (zQ * r)

theorem isPerpAx_perpPart (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    IsPerpAx hr (perpPart r v) := by
  have hσ := sgn_sq (centralCoord r)
  have hqE : qf (shortCls hr) (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = 32 := by
    rw [qf_axisE hr, uQ_dotProduct_uQ_self]
    norm_num
  constructor
  · change qf (shortCls hr) ((perpPart r v).1 : Matrix (Fin 24) (Fin 24) ℚ) = 0
    simp only [perpPart, bform_axis_left hr, bform_axis_zQ_left hr, Prod.fst_sub, Prod.smul_fst,
      Submodule.coe_sub, Submodule.coe_smul]
    rw [show ((axis r).1 : Matrix (Fin 24) (Fin 24) ℚ) = Am (axis r) from rfl,
      show ((axis (zQ * r)).1 : Matrix (Fin 24) (Fin 24) ℚ) = Am (axis (zQ * r)) from rfl,
      Am_axis, Am_axis_zQ hr]
    unfold qf
    simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hq : uQ (shortCls hr) ⬝ᵥ ((axisE r : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ uQ (shortCls hr)) = 32 :=
      hqE
    rw [hq]
    ring
  · change (perpPart r v).2.1 (shortCls hr) = 0
    simp only [perpPart, bform_axis_left hr, bform_axis_zQ_left hr, Prod.snd_sub, Prod.smul_snd,
      Prod.fst_sub, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (axis r).2.1 (shortCls hr) = xs (axis r) (shortCls hr) from rfl,
      show (axis (zQ * r)).2.1 (shortCls hr) = xs (axis (zQ * r)) (shortCls hr) from rfl,
      xs_axis_apply hr, ite_eq_left rfl, xs_axis_zQ_apply hr, ite_eq_left rfl]
    change xs v (shortCls hr) - _ - _ = 0
    linear_combination (-(xs v (shortCls hr))) * hσ

theorem eq_perpPart_add (r : Q) (v : SpaceB) :
    v = (bform v (axis r) / 8) • axis r + (bform v (axis (zQ * r)) / 8) • axis (zQ * r) +
      perpPart r v := by
  rw [perpPart]
  abel

theorem cubicQ_axis_self (hr : IsShortCoord (coordOf r)) :
    cubicQ (gmul (axis r)) (axis r) = (2976 : ℚ) • axis r := by
  rw [cubicQ_apply, axis_mul_self hr, map_smul, axis_mul_self hr, map_smul, map_smul,
    axis_mul_self hr]
  module

theorem cubicQ_axis_zQ (hr : IsShortCoord (coordOf r)) :
    cubicQ (gmul (axis r)) (axis (zQ * r)) = 0 := by
  rw [cubicQ_apply, axis_mul_axis_zQ hr]
  simp

theorem cubicQ_axis_eq (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    cubicQ (gmul (axis r)) v = (2976 * (bform v (axis r) / 8)) • axis r := by
  conv_lhs => rw [eq_perpPart_add r v]
  rw [map_add, map_add, map_smul, map_smul, cubicQ_axis_self hr, cubicQ_axis_zQ hr,
    cubicQ_axis_perp hr (isPerpAx_perpPart hr v), smul_zero, add_zero, add_zero, smul_smul,
    mul_comm]

theorem quartic_axis (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    gmul (axis r) (cubicQ (gmul (axis r)) v) - (16 : ℚ) • cubicQ (gmul (axis r)) v = 0 := by
  rw [cubicQ_axis_eq hr, map_smul, axis_mul_self hr, smul_smul, smul_smul, mul_comm, sub_self]

theorem cubicQ_of_eigenvalue (f : SpaceB →ₗ[ℚ] SpaceB) {v : SpaceB} {μ : ℚ} (hv : f v = μ • v) :
    cubicQ f v = (μ * μ * μ - 9 / 2 * (μ * μ) + 2 * μ) • v := by
  rw [cubicQ_apply, hv, map_smul, hv, map_smul, map_smul, hv]
  module

theorem axis_eigen16_iff (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    gmul (axis r) v = (16 : ℚ) • v ↔ v ∈ Submodule.span ℚ {axis r} := by
  constructor
  · intro hv
    have h1 := cubicQ_of_eigenvalue (gmul (axis r)) hv
    rw [cubicQ_axis_eq hr] at h1
    have h2 : v = ((2976 : ℚ)⁻¹ * (2976 * (bform v (axis r) / 8))) • axis r := by
      rw [← smul_smul, h1, smul_smul]
      norm_num
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_smul, axis_mul_self hr, smul_comm]

theorem isUnit_two_axis_sub (hr : IsShortCoord (coordOf r)) :
    IsUnit ((2 : ℚ) • gmul (axis r) - (16 : ℚ) • LinearMap.id) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at hv
  have h8 : gmul (axis r) v = (8 : ℚ) • v := by
    have := congrArg (fun w => (2 : ℚ)⁻¹ • w) hv
    simp only [smul_smul] at this
    norm_num at this
    exact this
  have hq := quartic_axis hr v
  rw [cubicQ_of_eigenvalue _ h8, map_smul, h8, smul_smul, smul_smul] at hq
  have hq' : (-1920 : ℚ) • v = 0 := by
    rw [← hq]
    module
  exact (smul_eq_zero.1 hq').resolve_left (by norm_num)

theorem axis_eigen_decomposition (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    ∃ v₁ v₂ v₃ v₄ : SpaceB, v = v₁ + v₂ + v₃ + v₄ ∧ gmul (axis r) v₁ = (16 : ℚ) • v₁ ∧
      gmul (axis r) v₂ = 0 ∧ gmul (axis r) v₃ = (4 : ℚ) • v₃ ∧
      gmul (axis r) v₄ = (1 / 2 : ℚ) • v₄ := by
  set L := gmul (axis r)
  set w := perpPart r v
  have hw : cubicQ L w = 0 := cubicQ_axis_perp hr (isPerpAx_perpPart hr v)
  rw [cubicQ_apply] at hw
  refine ⟨(bform v (axis r) / 8) • axis r,
    (bform v (axis (zQ * r)) / 8) • axis (zQ * r) +
      (1 / 2 : ℚ) • (L (L w) - (9 / 2 : ℚ) • L w + (2 : ℚ) • w),
    (1 / 14 : ℚ) • (L (L w) - (1 / 2 : ℚ) • L w),
    (-(4 / 7) : ℚ) • (L (L w) - (4 : ℚ) • L w), ?_, ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [eq_perpPart_add r v]
    module
  · rw [map_smul, axis_mul_self hr, smul_comm]
  · rw [map_add, map_smul, map_smul, axis_mul_axis_zQ hr, smul_zero, zero_add, map_add, map_sub,
      map_smul, map_smul]
    rw [show L (L (L w)) - (9 / 2 : ℚ) • L (L w) + (2 : ℚ) • L w = 0 from hw, smul_zero]
  · rw [map_smul, map_sub, map_smul]
    have : L (L (L w)) = (9 / 2 : ℚ) • L (L w) - (2 : ℚ) • L w := by
      rw [← sub_eq_zero, ← hw]
      module
    rw [this]
    module
  · rw [map_smul, map_sub, map_smul]
    have : L (L (L w)) = (9 / 2 : ℚ) • L (L w) - (2 : ℚ) • L w := by
      rw [← sub_eq_zero, ← hw]
      module
    rw [this]
    module

theorem inW_smul' (t : ℚ) (N : SpaceW) : inW (t • N) = t • inW N := by
  rw [inW, inW, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]

theorem axis_mul_inW (hr : IsShortCoord (coordOf r)) (N : SpaceW) :
    gmul (axis r) (inW N) = inW (N * ((4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ) +
      (2 : ℚ) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ)) -
      (4 : ℚ)⁻¹ • (((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * N *
        (1 - (8 : ℚ) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ)))) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun d => ?_) ?_)
  · rw [axisMul_A hr]
    simp
  · rw [axisMul_X hr]
    simp [qf_zero]
  · rw [axisMul_W hr, coe_Q_eq_sgn_smul_Rmat hr]
    change _ = N * ((4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ) +
      (2 : ℚ) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ)) -
      (4 : ℚ)⁻¹ • (sgn (centralCoord r) • Rmat (shortCls hr) * N *
        (1 - (8 : ℚ) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ)))
    simp only [Nm_inW, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
    module

theorem axis_mul_inW_neg (hr : IsShortCoord (coordOf r)) {N : SpaceW}
    (hN : ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * N = -N) :
    gmul (axis r) (inW N) = (2 : ℚ)⁻¹ • inW N := by
  rw [axis_mul_inW hr, hN, ← inW_smul']
  congr 1
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.neg_mul]
  module

theorem axis_mul_inW_pos_line (hr : IsShortCoord (coordOf r)) {N : SpaceW}
    (hN : ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * N = N)
    (hE : N * (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = N) :
    gmul (axis r) (inW N) = (4 : ℚ) • inW N := by
  rw [axis_mul_inW hr, hN, ← inW_smul']
  congr 1
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hE]
  module

theorem axis_mul_inW_pos_perp (hr : IsShortCoord (coordOf r)) {N : SpaceW}
    (hN : ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * N = N)
    (hE : N * (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = 0) :
    gmul (axis r) (inW N) = 0 := by
  rw [axis_mul_inW hr, hN]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hE, smul_zero,
    add_zero, sub_zero]
  rw [show (4 : ℚ)⁻¹ • N - (4 : ℚ)⁻¹ • N = 0 from sub_self _]
  rfl

theorem short_spin_axis_spectrum (r : Q) (hr : IsShortCoord (coordOf r)) :
    gmul (axis r) (axis r) = (16 : ℚ) • axis r ∧ bform (axis r) (axis r) = 8 ∧
    (∀ v, gmul (axis r) v = (16 : ℚ) • v ↔ v ∈ Submodule.span ℚ {axis r}) ∧
    (∀ v : SpaceB, ∃ v₁ v₂ v₃ v₄ : SpaceB, v = v₁ + v₂ + v₃ + v₄ ∧
      gmul (axis r) v₁ = (16 : ℚ) • v₁ ∧ gmul (axis r) v₂ = 0 ∧
      gmul (axis r) v₃ = (4 : ℚ) • v₃ ∧ gmul (axis r) v₄ = (1 / 2 : ℚ) • v₄) ∧
    iSupIndep (Module.End.eigenspace (gmul (axis r))) ∧
    (∀ v, gmul (axis r) (cubicQ (gmul (axis r)) v) - (16 : ℚ) • cubicQ (gmul (axis r)) v = 0) ∧
    (∀ v, cubicQ (gmul (axis r)) v = gmul (axis r) (gmul (axis r) (gmul (axis r) v)) -
      (9 / 2 : ℚ) • gmul (axis r) (gmul (axis r) v) + (2 : ℚ) • gmul (axis r) v) ∧
    IsUnit ((2 : ℚ) • gmul (axis r) - (16 : ℚ) • LinearMap.id) ∧
    (∀ N : SpaceW, gmul (axis r) (inW N) = inW (N * ((4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ) +
      (2 : ℚ) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ)) -
      (4 : ℚ)⁻¹ • (((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * N *
        (1 - (8 : ℚ) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ))))) ∧
    (∀ N : SpaceW, ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * N = -N →
      gmul (axis r) (inW N) = (2 : ℚ)⁻¹ • inW N) ∧
    (∀ N : SpaceW, ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * N = N →
      N * (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = N → gmul (axis r) (inW N) = (4 : ℚ) • inW N) ∧
    (∀ N : SpaceW, ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * N = N →
      N * (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = 0 → gmul (axis r) (inW N) = 0) :=
  ⟨axis_mul_self hr, bform_axis_self hr, axis_eigen16_iff hr, axis_eigen_decomposition hr,
    Module.End.eigenspaces_iSupIndep _, quartic_axis hr, fun _ => rfl, isUnit_two_axis_sub hr,
    axis_mul_inW hr, fun _ hN => axis_mul_inW_neg hr hN,
    fun _ hN hE => axis_mul_inW_pos_line hr hN hE, fun _ hN hE => axis_mul_inW_pos_perp hr hN hE⟩

end CFSG.Monster.Griess
