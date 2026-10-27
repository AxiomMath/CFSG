module

public import CFSG.Monster.Griess.AxisSpectrum
public import CFSG.Monster.Visible.Action

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.ScalarKernel Matrix

@[expose] noncomputable def axisCubic {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : M →ₗ[ℚ] M) : M →ₗ[ℚ] M :=
  f ∘ₗ (f - (4 : ℚ) • LinearMap.id) ∘ₗ (f - (16 : ℚ) • LinearMap.id)

theorem axisCubic_apply {M : Type*} [AddCommGroup M] [Module ℚ M] (f : M →ₗ[ℚ] M) (x : M) :
    axisCubic f x = f (f (f x)) - (20 : ℚ) • f (f x) + (64 : ℚ) • f x := by
  simp only [axisCubic, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul]
  module

theorem axisCubic_of_eigen {M : Type*} [AddCommGroup M] [Module ℚ M] (f : M →ₗ[ℚ] M) {x : M}
    {μ : ℚ} (hx : f x = μ • x) :
    axisCubic f x = (μ * (μ - 4) * (μ - 16)) • x := by
  rw [axisCubic_apply, hx, map_smul, hx, map_smul, map_smul, hx]
  module

theorem axisCubic_of_sq {M : Type*} [AddCommGroup M] [Module ℚ M] (f : M →ₗ[ℚ] M) {x : M}
    (hx : f (f x) = (4 : ℚ) • f x) : axisCubic f x = 0 := by
  rw [axisCubic_apply, hx, map_smul, hx]
  module

theorem rhoEquiv_fst (r : Q) (w : SpaceB) : (rhoEquiv r w).1 = w.1 := thetaA_one w.1

theorem rhoEquiv_snd_fst (r : Q) (w : SpaceB) :
    (rhoEquiv r w).2.1 = thetaX (rhoPair r) w.2.1 := rfl

theorem rhoEquiv_snd_snd (r : Q) (w : SpaceB) :
    (rhoEquiv r w).2.2 = ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)ᵀ * w.2.2 := by
  show ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)ᵀ * w.2.2 * mat 1 = _
  rw [mat_one, Matrix.mul_one]

theorem symm_conj (r t : Q) : spinEquiv.symm (r⁻¹ * t * r) =
    (spinEquiv.symm r)⁻¹ * spinEquiv.symm t * spinEquiv.symm r :=
  (map_mul spinEquiv.symm (r⁻¹ * t) r).trans (congrArg (· * spinEquiv.symm r)
    ((map_mul spinEquiv.symm r⁻¹ t).trans
      (congrArg (· * spinEquiv.symm t) (map_inv spinEquiv.symm r))))

private theorem two_eq_zero_zmod : (2 : ZMod 2) = 0 := rfl

private theorem add_self_cocode (δ : Cocode) : δ + δ = 0 := by
  rw [← two_smul (ZMod 2) δ, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem spinCoord_conj (x y : SpinCoord) :
    x⁻¹ * y * x = ⟨y.s + pair y.a x.δ + pair x.a y.δ, y.a, y.δ⟩ := by
  ext
  · simp only [SpinCoord.mul_s, SpinCoord.inv_s, SpinCoord.inv_δ, SpinCoord.mul_δ,
      pair_add_right]
    linear_combination (x.s + pair x.a x.δ) * two_eq_zero_zmod
  · simp only [SpinCoord.mul_a, SpinCoord.inv_a]
    rw [add_comm x.a y.a, add_assoc, add_self_C, add_zero]
  · simp only [SpinCoord.mul_δ, SpinCoord.inv_δ]
    rw [add_comm x.δ y.δ, add_assoc, add_self_cocode, add_zero]

theorem symm_conj_rep (r : Q) (p : C × Cocode) :
    spinEquiv.symm (r⁻¹ * rep p * r) =
      ⟨pair p.1 (coordOf r).2 + pair (coordOf r).1 p.2, p.1, p.2⟩ := by
  have h2 : spinEquiv.symm (rep p) = ⟨0, p.1, p.2⟩ := spinEquiv.symm_apply_apply _
  refine (symm_conj r (rep p)).trans ?_
  rw [h2, spinCoord_conj, zero_add]
  rfl

theorem pair_add_pair_eq_alphaS (c d : ShortIdx) :
    pair d.1.1 c.1.2 + pair c.1.1 d.1.2 = ((alphaS c d : ℤ) : ZMod 2) := by
  have h1 := bL_phi0 c.1.1 d.1.1 c.1.2 d.1.2
  have hc : phi0 (c.1.1, c.1.2) = cls (uvec c) (uvec_mem c).1 :=
    (classOf_uvec c).symm.trans (classOf_of_mem' (uvec_mem c).1)
  have hd : phi0 (d.1.1, d.1.2) = cls (uvec d) (uvec_mem d).1 :=
    (classOf_uvec d).symm.trans (classOf_of_mem' (uvec_mem d).1)
  rw [hc, hd, bL_cls] at h1
  rw [add_comm]
  exact h1.symm

theorem xlift_conj_rep {r : Q} (hr : IsShortCoord (coordOf r)) (d : ShortIdx) :
    Xlift (r⁻¹ * rep d.1 * r) =
      sgn ((alphaS (shortCls hr) d : ℤ) : ZMod 2) • (Pi.single d 1 : SpaceX) := by
  have hs := symm_conj_rep r d.1
  have hco : coordOf (r⁻¹ * rep d.1 * r) = d.1 := by
    rw [coordOf, hs]
  have hcc : centralCoord (r⁻¹ * rep d.1 * r) = ((alphaS (shortCls hr) d : ℤ) : ZMod 2) := by
    rw [centralCoord, hs]
    exact pair_add_pair_eq_alphaS (shortCls hr) d
  have hsh : IsShortCoord (coordOf (r⁻¹ * rep d.1 * r)) := by rw [hco]; exact d.2
  rw [Xlift_eq hsh, hcc]
  congr 2
  exact Subtype.ext hco

theorem thetaX_rhoPair_single {r : Q} (hr : IsShortCoord (coordOf r)) (d : ShortIdx) :
    thetaX (rhoPair r) (Pi.single d 1) =
      sgn ((alphaS (shortCls hr) d : ℤ) : ZMod 2) • (Pi.single d 1 : SpaceX) := by
  rw [thetaX_single, conjQ_rhoPair]
  exact xlift_conj_rep hr d

private theorem sub_smul_smul_eq {M : Type*} [AddCommGroup M] [Module ℚ M] (x : M) (t s : ℚ)
    (h : 1 - 16 / 217 * t = s) : x - (16 / 217 : ℚ) • (t • x) = s • x := by
  rw [← h, sub_smul, one_smul, smul_smul]

theorem F_Kop_single {σ : ℚ} (hσ : σ * σ = 1) {c d : ShortIdx} (hcd : d ≠ c) :
    (Pi.single d 1 : SpaceX) - (16 / 217 : ℚ) • axisCubic (Kop σ c) (Pi.single d 1) =
      sgn ((alphaS c d : ℤ) : ZMod 2) • (Pi.single d 1 : SpaceX) := by
  by_cases h : IsShortCoord (c.1 + d.1)
  ·
    obtain ⟨e, he⟩ : ∃ e : ShortIdx, e.1 = c.1 + d.1 := ⟨⟨_, h⟩, rfl⟩
    have he' : d.1 = c.1 + e.1 := by rw [he, add_add_cancel_coord]
    have hα2 : alphaS c d = 2 ∨ alphaS c d = -2 := (isShortCoord_add_iff (Ne.symm hcd)).1 h
    have hα : alphaS d c ^ 2 = 4 := by
      rcases hα2 with h2 | h2 <;> rw [alphaS_comm, h2] <;> norm_num
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
    have hsq : Kop σ c (Kop σ c (Pi.single d 1)) = (4 : ℚ) • Kop σ c (Pi.single d 1) := by
      rw [k1, map_sub, map_smul, map_smul, k1, k2]
      generalize 2 * σ * sgn (pair d.1.1 c.1.2) = s at hss ⊢
      have e2 : (2 : ℚ) • ((2 : ℚ) • Pi.single d 1 - s • Pi.single e 1) -
          s • ((2 : ℚ) • Pi.single e 1 - s • Pi.single d 1) =
          (4 + s * s) • (Pi.single d 1 : SpaceX) - (4 * s) • Pi.single e 1 := by
        module
      rw [e2, hss]
      module
    have hsign : ((alphaS c d : ℤ) : ZMod 2) = 0 := by
      rcases hα2 with h2 | h2 <;> rw [h2] <;> rfl
    rw [axisCubic_of_sq _ hsq, smul_zero, sub_zero, hsign, sgn_zero, one_smul]
  ·
    have hK := Kop_single_of_not_short σ h
    rw [axisCubic_of_eigen _ hK, betaX_eq, alphaS_comm d c]
    apply sub_smul_smul_eq
    rcases alphaS_mem (Ne.symm hcd) with h2 | h2 | h2 | h2 | h2
    · exact absurd ((isShortCoord_add_iff (Ne.symm hcd)).2 (Or.inr h2)) h
    · rw [h2, show (((-1 : ℤ) : ZMod 2)) = 1 from rfl, show sgn 1 = -1 from rfl]
      norm_num
    · rw [h2, show (((0 : ℤ) : ZMod 2)) = 0 from rfl, sgn_zero]
      norm_num
    · rw [h2, show (((1 : ℤ) : ZMod 2)) = 1 from rfl, show sgn 1 = -1 from rfl]
      norm_num
    · exact absurd ((isShortCoord_add_iff (Ne.symm hcd)).2 (Or.inl h2)) h

theorem thetaX_rhoPair_eq {r : Q} (hr : IsShortCoord (coordOf r)) {x : SpaceX}
    (hx : x (shortCls hr) = 0) :
    thetaX (rhoPair r) x =
      x - (16 / 217 : ℚ) • axisCubic (Kop (sgn (centralCoord r)) (shortCls hr)) x := by
  have hσ := sgn_sq (centralCoord r)
  have hdec : x = ∑ d, x d • (Pi.single d 1 : SpaceX) := by
    funext e
    simp [Finset.sum_apply, Pi.single_apply]
  have key : ∀ d, x d • thetaX (rhoPair r) (Pi.single d 1) =
      x d • ((Pi.single d 1 : SpaceX) - (16 / 217 : ℚ) •
        axisCubic (Kop (sgn (centralCoord r)) (shortCls hr)) (Pi.single d 1)) := by
    intro d
    by_cases hd : d = shortCls hr
    · have hxd : x d = 0 := by rw [hd]; exact hx
      rw [hxd, zero_smul, zero_smul]
    · rw [thetaX_rhoPair_single hr d, F_Kop_single hσ hd]
  calc thetaX (rhoPair r) x = thetaX (rhoPair r) (∑ d, x d • (Pi.single d 1 : SpaceX)) :=
        congrArg _ hdec
    _ = ∑ d, x d • thetaX (rhoPair r) (Pi.single d 1) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
    _ = ∑ d, x d • ((Pi.single d 1 : SpaceX) - (16 / 217 : ℚ) •
          axisCubic (Kop (sgn (centralCoord r)) (shortCls hr)) (Pi.single d 1)) :=
        Finset.sum_congr rfl fun d _ => key d
    _ = (∑ d, x d • (Pi.single d 1 : SpaceX)) - (16 / 217 : ℚ) •
          axisCubic (Kop (sgn (centralCoord r)) (shortCls hr))
            (∑ d, x d • (Pi.single d 1 : SpaceX)) := by
        rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [map_smul, smul_sub, smul_comm]
    _ = _ := by rw [← hdec]

theorem F_LWop {σ : ℚ} (hσ : σ = 1 ∨ σ = -1) {R : Matrix SpinIdx SpinIdx ℚ}
    (hR : R * R = 1) {E : Matrix (Fin 24) (Fin 24) ℚ} (hE : E * E = E) (N : SpaceW) :
    N - (16 / 217 : ℚ) • axisCubic (LWop σ R E) N = σ • (R * N) := by
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
  rw [axisCubic_apply]
  simp only [map_add, map_sub, map_smul, a1, a2, a3, a4]
  rcases hσ with rfl | rfl <;> module

theorem rhoEquiv_axis_of_conj (r t : Q) (h : r⁻¹ * t * r = t) :
    rhoEquiv r (axis t) = axis t := by
  have h1 := rhoEquiv_symMat r (axisE t)
  have h2 : rhoEquiv r (0, Xlift t, 0) = (0, Xlift t, 0) :=
    (rhoEquiv_Xlift r t).trans (congrArg (fun u => ((0 : symMat), Xlift u, (0 : SpaceW))) h)
  calc rhoEquiv r (axis t) = (2 : ℚ) • rhoEquiv r (axisE t, 0, 0) -
        (2 : ℚ) • rhoEquiv r (0, Xlift t, 0) := by
        rw [axis, map_sub, map_smul, map_smul]
    _ = (2 : ℚ) • ((axisE t, 0, 0) : SpaceB) - (2 : ℚ) • ((0, Xlift t, 0) : SpaceB) :=
        congrArg₂ (fun a b => (2 : ℚ) • a - (2 : ℚ) • b) h1 h2
    _ = axis t := rfl

theorem rhoEquiv_axis (r : Q) : rhoEquiv r (axis r) = axis r :=
  rhoEquiv_axis_of_conj r r (by group)

theorem rhoEquiv_axis_zQ (r : Q) : rhoEquiv r (axis (zQ * r)) = axis (zQ * r) := by
  have hzc : zQ ∈ Subgroup.center Q := center_Q ▸ Subgroup.mem_zpowers zQ
  have hz : zQ * r = r * zQ := (Subgroup.mem_center_iff.1 hzc r).symm
  refine rhoEquiv_axis_of_conj r (zQ * r) ?_
  calc r⁻¹ * (zQ * r) * r = r⁻¹ * (r * zQ) * r := by rw [hz]
    _ = zQ * r := by group

theorem rhoEquiv_perp {r : Q} (hr : IsShortCoord (coordOf r)) {w : SpaceB}
    (hw : IsPerpAx hr w) :
    rhoEquiv r w = w - (16 / 217 : ℚ) • axisCubic (gmul (axis r)) w := by
  have hw1 := isPerpAx_gmul hr hw
  have hw2 := isPerpAx_gmul hr hw1
  rw [axisCubic_apply]
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  ·
    have h1 : Am (gmul (axis r) w) = MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Am w) :=
      axisMul_A_perp hr hw
    have h2 : Am (gmul (axis r) (gmul (axis r) w)) =
        (4 : ℚ) • MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Am w) := by
      have := axisMul_A_perp hr hw1
      change Am (gmul (axis r) (gmul (axis r) w)) =
        MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Am (gmul (axis r) w)) at this
      rw [this, h1]
      exact MAop_MAop hr hw.1
    have h3 : Am (gmul (axis r) (gmul (axis r) (gmul (axis r) w))) =
        (16 : ℚ) • MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Am w) := by
      have := axisMul_A_perp hr hw2
      change Am (gmul (axis r) (gmul (axis r) (gmul (axis r) w))) =
        MAop (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Am (gmul (axis r) (gmul (axis r) w)))
        at this
      rw [this, h2, map_smul, MAop_MAop hr hw.1, smul_smul]
      norm_num
    rw [rhoEquiv_fst]
    change Am w = Am (w - (16 / 217 : ℚ) • (gmul (axis r) (gmul (axis r) (gmul (axis r) w)) -
      (20 : ℚ) • gmul (axis r) (gmul (axis r) w) + (64 : ℚ) • gmul (axis r) w))
    have e : ∀ u v t : SpaceB, Am (w - (16 / 217 : ℚ) • (u - (20 : ℚ) • v + (64 : ℚ) • t)) =
        Am w - (16 / 217 : ℚ) • (Am u - (20 : ℚ) • Am v + (64 : ℚ) • Am t) := by
      intro u v t
      simp only [Am, Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Submodule.coe_sub,
        Submodule.coe_add, Submodule.coe_smul]
    rw [e, h1, h2, h3]
    module
  ·
    have h1 : xs (gmul (axis r) w) = Kop (sgn (centralCoord r)) (shortCls hr) (xs w) :=
      axisMul_X_perp hr hw
    have h2 : xs (gmul (axis r) (gmul (axis r) w)) = Kop (sgn (centralCoord r)) (shortCls hr)
        (Kop (sgn (centralCoord r)) (shortCls hr) (xs w)) := by
      have := axisMul_X_perp hr hw1
      change xs (gmul (axis r) (gmul (axis r) w)) =
        Kop (sgn (centralCoord r)) (shortCls hr) (xs (gmul (axis r) w)) at this
      rw [this, h1]
    have h3 : xs (gmul (axis r) (gmul (axis r) (gmul (axis r) w))) =
        Kop (sgn (centralCoord r)) (shortCls hr) (Kop (sgn (centralCoord r)) (shortCls hr)
          (Kop (sgn (centralCoord r)) (shortCls hr) (xs w))) := by
      have := axisMul_X_perp hr hw2
      change xs (gmul (axis r) (gmul (axis r) (gmul (axis r) w))) =
        Kop (sgn (centralCoord r)) (shortCls hr) (xs (gmul (axis r) (gmul (axis r) w))) at this
      rw [this, h2]
    rw [rhoEquiv_snd_fst, thetaX_rhoPair_eq hr hw.2, axisCubic_apply]
    change _ = xs (w - (16 / 217 : ℚ) • (gmul (axis r) (gmul (axis r) (gmul (axis r) w)) -
      (20 : ℚ) • gmul (axis r) (gmul (axis r) w) + (64 : ℚ) • gmul (axis r) w))
    have e : ∀ u v t : SpaceB, xs (w - (16 / 217 : ℚ) • (u - (20 : ℚ) • v + (64 : ℚ) • t)) =
        xs w - (16 / 217 : ℚ) • (xs u - (20 : ℚ) • xs v + (64 : ℚ) • xs t) := by
      intro u v t
      simp only [xs, Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.fst_sub, Prod.fst_add,
        Prod.smul_fst]
    rw [e, h1, h2, h3]
  ·
    have h1 : Nm (gmul (axis r) w) = LWop (sgn (centralCoord r)) (Rmat (shortCls hr))
        (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Nm w) := axisMul_W' hr w
    have h2 : Nm (gmul (axis r) (gmul (axis r) w)) = LWop (sgn (centralCoord r))
        (Rmat (shortCls hr)) (axisE r : Matrix (Fin 24) (Fin 24) ℚ)
        (LWop (sgn (centralCoord r)) (Rmat (shortCls hr))
          (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Nm w)) := by
      have := axisMul_W' hr (gmul (axis r) w)
      change Nm (gmul (axis r) (gmul (axis r) w)) = LWop (sgn (centralCoord r))
        (Rmat (shortCls hr)) (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Nm (gmul (axis r) w))
        at this
      rw [this, h1]
    have h3 : Nm (gmul (axis r) (gmul (axis r) (gmul (axis r) w))) = LWop (sgn (centralCoord r))
        (Rmat (shortCls hr)) (axisE r : Matrix (Fin 24) (Fin 24) ℚ)
        (LWop (sgn (centralCoord r)) (Rmat (shortCls hr))
          (axisE r : Matrix (Fin 24) (Fin 24) ℚ)
          (LWop (sgn (centralCoord r)) (Rmat (shortCls hr))
            (axisE r : Matrix (Fin 24) (Fin 24) ℚ) (Nm w))) := by
      have := axisMul_W' hr (gmul (axis r) (gmul (axis r) w))
      change Nm (gmul (axis r) (gmul (axis r) (gmul (axis r) w))) = LWop (sgn (centralCoord r))
        (Rmat (shortCls hr)) (axisE r : Matrix (Fin 24) (Fin 24) ℚ)
        (Nm (gmul (axis r) (gmul (axis r) w))) at this
      rw [this, h2]
    have hF := F_LWop (sgn_eq_one_or (centralCoord r)) (Rmat_mul_self (shortCls hr))
      (axisE_mul_self hr) (Nm w)
    rw [axisCubic_apply] at hF
    have hr' : ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)ᵀ =
        sgn (centralCoord r) • Rmat (shortCls hr) := by
      rw [coe_Q_eq_sgn_smul_Rmat hr, transpose_smul, Rmat_symm]
    rw [rhoEquiv_snd_snd, hr', Matrix.smul_mul]
    change _ = Nm (w - (16 / 217 : ℚ) • (gmul (axis r) (gmul (axis r) (gmul (axis r) w)) -
      (20 : ℚ) • gmul (axis r) (gmul (axis r) w) + (64 : ℚ) • gmul (axis r) w))
    have e : ∀ u v t : SpaceB, Nm (w - (16 / 217 : ℚ) • (u - (20 : ℚ) • v + (64 : ℚ) • t)) =
        Nm w - (16 / 217 : ℚ) • (Nm u - (20 : ℚ) • Nm v + (64 : ℚ) • Nm t) := by
      intro u v t
      simp only [Nm, Prod.snd_sub, Prod.snd_add, Prod.smul_snd]
    rw [e, h1, h2, h3]
    exact hF.symm

theorem rhoEquiv_eq_axisPoly {r : Q} (hr : IsShortCoord (coordOf r)) (v : SpaceB) :
    rhoEquiv r v = v - (16 / 217 : ℚ) • axisCubic (gmul (axis r)) v := by
  have ha : axisCubic (gmul (axis r)) (axis r) = 0 := by
    rw [axisCubic_of_eigen _ (axis_mul_self hr)]
    norm_num
  have ha' : axisCubic (gmul (axis r)) (axis (zQ * r)) = 0 := by
    have h0 : gmul (axis r) (axis (zQ * r)) = (0 : ℚ) • axis (zQ * r) := by
      rw [zero_smul]
      exact axis_mul_axis_zQ hr
    rw [axisCubic_of_eigen _ h0]
    norm_num
  have hv := eq_perpPart_add r v
  have hw := isPerpAx_perpPart hr v
  have h1 : rhoEquiv r v = (bform v (axis r) / 8) • axis r +
      (bform v (axis (zQ * r)) / 8) • axis (zQ * r) + rhoEquiv r (perpPart r v) := by
    calc rhoEquiv r v = rhoEquiv r ((bform v (axis r) / 8) • axis r +
          (bform v (axis (zQ * r)) / 8) • axis (zQ * r) + perpPart r v) := congrArg _ hv
      _ = (bform v (axis r) / 8) • rhoEquiv r (axis r) +
          (bform v (axis (zQ * r)) / 8) • rhoEquiv r (axis (zQ * r)) +
          rhoEquiv r (perpPart r v) := by
        simp only [map_add, map_smul]
      _ = _ := by rw [rhoEquiv_axis, rhoEquiv_axis_zQ]
  have h2 : axisCubic (gmul (axis r)) v = axisCubic (gmul (axis r)) (perpPart r v) := by
    calc axisCubic (gmul (axis r)) v = axisCubic (gmul (axis r)) ((bform v (axis r) / 8) • axis r +
          (bform v (axis (zQ * r)) / 8) • axis (zQ * r) + perpPart r v) := congrArg _ hv
      _ = (bform v (axis r) / 8) • axisCubic (gmul (axis r)) (axis r) +
          (bform v (axis (zQ * r)) / 8) • axisCubic (gmul (axis r)) (axis (zQ * r)) +
          axisCubic (gmul (axis r)) (perpPart r v) := by
        simp only [map_add, map_smul]
      _ = _ := by rw [ha, ha', smul_zero, smul_zero, zero_add, zero_add]
  rw [h1, h2, rhoEquiv_perp hr hw]
  calc _ = ((bform v (axis r) / 8) • axis r + (bform v (axis (zQ * r)) / 8) • axis (zQ * r) +
        perpPart r v) - (16 / 217 : ℚ) • axisCubic (gmul (axis r)) (perpPart r v) := by abel
    _ = _ := by rw [← hv]

theorem short_axis_polynomial_involution (r : Q) (hr : IsShortCoord (coordOf r)) :
    (rhoEquiv r : SpaceB →ₗ[ℚ] SpaceB) = LinearMap.id - (16 / 217 : ℚ) •
      (gmul (axis r) ∘ₗ (gmul (axis r) - (4 : ℚ) • LinearMap.id) ∘ₗ
        (gmul (axis r) - (16 : ℚ) • LinearMap.id)) ∧
    (∀ v ∈ Module.End.eigenspace (gmul (axis r)) (1 / 2 : ℚ), rhoEquiv r v = -v) ∧
    (∀ v ∈ Module.End.eigenspace (gmul (axis r)) 0, rhoEquiv r v = v) ∧
    (∀ v ∈ Module.End.eigenspace (gmul (axis r)) 4, rhoEquiv r v = v) ∧
    (∀ v ∈ Module.End.eigenspace (gmul (axis r)) 16, rhoEquiv r v = v) := by
  have hev : ∀ (μ : ℚ) (v : SpaceB), v ∈ Module.End.eigenspace (gmul (axis r)) μ →
      rhoEquiv r v = (1 - 16 / 217 * (μ * (μ - 4) * (μ - 16))) • v := by
    intro μ v hv
    rw [rhoEquiv_eq_axisPoly hr, axisCubic_of_eigen _ (Module.End.mem_eigenspace_iff.1 hv)]
    exact sub_smul_smul_eq v _ _ rfl
  refine ⟨LinearMap.ext fun v => rhoEquiv_eq_axisPoly hr v, fun v hv => ?_, fun v hv => ?_,
    fun v hv => ?_, fun v hv => ?_⟩
  · rw [hev _ v hv, show (1 - 16 / 217 * (1 / 2 * (1 / 2 - 4) * (1 / 2 - 16)) : ℚ) = -1 by
      norm_num]
    exact neg_one_smul ℚ v
  · rw [hev _ v hv]; norm_num
  · rw [hev _ v hv]; norm_num
  · rw [hev _ v hv]; norm_num

end CFSG.Monster.B
