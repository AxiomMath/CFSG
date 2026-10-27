module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Galois.Basic

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module Matrix

structure QuadData (K E : Type*) [Field K] [Field E] [Algebra K E] where
  bar : E ≃ₐ[K] E
  bar_bar : ∀ z, bar (bar z) = z
  ω : E
  t : K
  n : K
  basis : Basis (Fin 2) K E
  basis_zero : basis 0 = 1
  basis_one : basis 1 = ω
  bar_ω : bar ω = algebraMap K E t - ω
  sq : ω * ω = algebraMap K E t * ω - algebraMap K E n
  bar_ne : bar ω ≠ ω

namespace QuadData

variable {K E : Type*} [Field K] [Field E] [Algebra K E] (D : QuadData K E)

@[expose] noncomputable def X (z : E) : K := D.basis.repr z 0

@[expose] noncomputable def Y (z : E) : K := D.basis.repr z 1

theorem repr_eq (z : E) : z = algebraMap K E (D.X z) + algebraMap K E (D.Y z) * D.ω := by
  have h := D.basis.sum_repr z
  rw [Fin.sum_univ_two, D.basis_zero, D.basis_one] at h
  conv_lhs => rw [← h]
  simp [X, Y, Algebra.smul_def]

theorem coords_unique {x y : K} {z : E} (h : z = algebraMap K E x + algebraMap K E y * D.ω) :
    D.X z = x ∧ D.Y z = y := by
  have h2 : z = ∑ i, (![x, y] i) • D.basis i := by
    rw [Fin.sum_univ_two, D.basis_zero, D.basis_one]
    simpa [Algebra.smul_def] using h
  have h3 := D.basis.repr_sum_self ![x, y]
  rw [← h2] at h3
  exact ⟨by simpa [X] using congrFun h3 0, by simpa [Y] using congrFun h3 1⟩

theorem ext_coords {z w : E} (hX : D.X z = D.X w) (hY : D.Y z = D.Y w) : z = w := by
  rw [D.repr_eq z, D.repr_eq w, hX, hY]

theorem exists_coords (z : E) :
    ∃ x y : K, z = algebraMap K E x + algebraMap K E y * D.ω ∧ D.X z = x ∧ D.Y z = y :=
  ⟨D.X z, D.Y z, D.repr_eq z, rfl, rfl⟩

theorem X_add (z w : E) : D.X (z + w) = D.X z + D.X w := by simp [X]

theorem Y_add (z w : E) : D.Y (z + w) = D.Y z + D.Y w := by simp [Y]

theorem X_smul (r : K) (z : E) : D.X (r • z) = r * D.X z := by simp [X]

theorem Y_smul (r : K) (z : E) : D.Y (r • z) = r * D.Y z := by simp [Y]

theorem X_algebraMap (x : K) : D.X (algebraMap K E x) = x :=
  (D.coords_unique (y := 0) (by simp)).1

theorem Y_algebraMap (x : K) : D.Y (algebraMap K E x) = 0 :=
  (D.coords_unique (x := x) (y := 0) (by simp)).2

theorem X_one : D.X 1 = 1 := by simpa using D.X_algebraMap 1

theorem Y_one : D.Y 1 = 0 := by simpa using D.Y_algebraMap 1

theorem X_ω : D.X D.ω = 0 := (D.coords_unique (x := 0) (y := 1) (by simp)).1

theorem Y_ω : D.Y D.ω = 1 := (D.coords_unique (x := 0) (y := 1) (by simp)).2

theorem X_mul (z w : E) : D.X (z * w) = D.X z * D.X w - D.n * (D.Y z * D.Y w) := by
  refine (D.coords_unique (y := D.X z * D.Y w + D.Y z * D.X w + D.t * (D.Y z * D.Y w)) ?_).1
  conv_lhs => rw [D.repr_eq z, D.repr_eq w]
  simp only [map_sub, map_add, map_mul]
  linear_combination (algebraMap K E (D.Y z) * algebraMap K E (D.Y w)) * D.sq

theorem Y_mul (z w : E) :
    D.Y (z * w) = D.X z * D.Y w + D.Y z * D.X w + D.t * (D.Y z * D.Y w) := by
  refine (D.coords_unique (x := D.X z * D.X w - D.n * (D.Y z * D.Y w)) ?_).2
  conv_lhs => rw [D.repr_eq z, D.repr_eq w]
  simp only [map_sub, map_add, map_mul]
  linear_combination (algebraMap K E (D.Y z) * algebraMap K E (D.Y w)) * D.sq

theorem bar_eq (x y : K) :
    D.bar (algebraMap K E x + algebraMap K E y * D.ω) =
      algebraMap K E (x + D.t * y) + algebraMap K E (-y) * D.ω := by
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, D.bar_ω]
  simp only [map_add, map_mul, map_neg]
  ring

theorem X_bar (z : E) : D.X (D.bar z) = D.X z + D.t * D.Y z := by
  obtain ⟨x, y, hz, hx, hy⟩ := D.exists_coords z
  rw [hx, hy]
  subst hz
  exact (D.coords_unique (D.bar_eq x y)).1

theorem Y_bar (z : E) : D.Y (D.bar z) = -D.Y z := by
  obtain ⟨x, y, hz, -, hy⟩ := D.exists_coords z
  rw [hy]
  subst hz
  exact (D.coords_unique (D.bar_eq x y)).2

@[expose] noncomputable def Nm (z : E) : K := D.X z ^ 2 + D.t * D.X z * D.Y z + D.n * D.Y z ^ 2

theorem algebraMap_Nm (z : E) : algebraMap K E (D.Nm z) = z * D.bar z := by
  obtain ⟨x, y, hz, hx, hy⟩ := D.exists_coords z
  rw [Nm, hx, hy]
  subst hz
  rw [D.bar_eq]
  simp only [map_add, map_mul, map_pow, map_neg]
  linear_combination (algebraMap K E y) ^ 2 * D.sq

theorem Nm_mul (z w : E) : D.Nm (z * w) = D.Nm z * D.Nm w := by
  refine (algebraMap K E).injective ?_
  rw [map_mul, D.algebraMap_Nm, D.algebraMap_Nm, D.algebraMap_Nm, map_mul]
  ring

theorem Nm_eq_zero {z : E} (hz : z * D.bar z = 0) : z = 0 := by
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · simpa using h

theorem Nm_one : D.Nm 1 = 1 := by
  simp [Nm, D.X_one, D.Y_one]

@[expose] noncomputable def tr (z : E) : K := 2 * D.X z + D.t * D.Y z

theorem algebraMap_tr (z : E) : algebraMap K E (D.tr z) = z + D.bar z := by
  obtain ⟨x, y, hz, hx, hy⟩ := D.exists_coords z
  rw [tr, hx, hy]
  subst hz
  rw [D.bar_eq]
  simp only [map_add, map_mul, map_neg, map_ofNat]
  ring

theorem tr_add_Nm (z : E) : D.Nm (z + 1) = D.Nm z + D.tr z + 1 := by
  simp [Nm, tr, D.X_add, D.Y_add, D.X_one, D.Y_one]
  ring

@[expose] noncomputable def lmat (z : E) : Matrix (Fin 2) (Fin 2) K :=
  !![D.X z, -(D.n * D.Y z); D.Y z, D.X z + D.t * D.Y z]

@[expose] def cmat : Matrix (Fin 2) (Fin 2) K := !![1, D.t; 0, -1]

theorem lmat_mul (z w : E) : D.lmat (z * w) = D.lmat z * D.lmat w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lmat, Matrix.mul_apply, Fin.sum_univ_two, D.X_mul, D.Y_mul] <;> ring

theorem lmat_one : D.lmat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lmat, D.X_one, D.Y_one]

theorem lmat_add (z w : E) : D.lmat (z + w) = D.lmat z + D.lmat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lmat, D.X_add, D.Y_add] <;> ring

theorem lmat_smul (r : K) (z : E) : D.lmat (r • z) = r • D.lmat z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lmat, D.X_smul, D.Y_smul] <;> ring

theorem lmat_det (z : E) : (D.lmat z).det = D.Nm z := by
  rw [Matrix.det_fin_two]
  simp [lmat, Nm]
  ring

theorem cmat_mul_cmat : D.cmat * D.cmat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmat, Matrix.mul_apply, Fin.sum_univ_two]

theorem cmat_mul_lmat (z : E) : D.cmat * D.lmat z = D.lmat (D.bar z) * D.cmat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmat, lmat, Matrix.mul_apply, Fin.sum_univ_two, D.X_bar, D.Y_bar] <;> ring

theorem trace_lmat_mul_cmat (w : E) : (D.lmat w * D.cmat).trace = 0 := by
  simp [Matrix.trace_fin_two, lmat, cmat]
  ring

theorem cmat_det : D.cmat.det = -1 := by
  rw [Matrix.det_fin_two]
  simp [cmat]

theorem lmat_mulVec (w u : E) :
    D.lmat w *ᵥ ![D.X u, D.Y u] = ![D.X (w * u), D.Y (w * u)] := by
  ext i
  fin_cases i <;> simp [lmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, D.X_mul, D.Y_mul] <;>
    ring

theorem cmat_mulVec (u : E) :
    D.cmat *ᵥ ![D.X u, D.Y u] = ![D.X (D.bar u), D.Y (D.bar u)] := by
  ext i
  fin_cases i <;> simp [cmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, D.X_bar, D.Y_bar]

@[expose] noncomputable def phi (c : E) (w : E × E) : Matrix (Fin 2) (Fin 2) K :=
  D.lmat w.1 + D.lmat (c * w.2) * D.cmat

theorem phi_add (c : E) (w w' : E × E) : D.phi c (w + w') = D.phi c w + D.phi c w' := by
  simp only [phi, Prod.fst_add, Prod.snd_add, mul_add, D.lmat_add, Matrix.add_mul]
  abel

theorem phi_smul (c : E) (r : K) (w : E × E) : D.phi c (r • w) = r • D.phi c w := by
  have h : c * (r • w.2) = r • (c * w.2) := by rw [mul_smul_comm]
  simp only [phi, Prod.smul_fst, Prod.smul_snd, h, D.lmat_smul, Matrix.smul_mul, smul_add]

@[expose] noncomputable def phiL (c : E) : (E × E) →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun := D.phi c
  map_add' := D.phi_add c
  map_smul' := D.phi_smul c

theorem det_phi (c : E) (w : E × E) : (D.phi c w).det = D.Nm w.1 - D.Nm (c * w.2) := by
  rw [Matrix.det_fin_two]
  simp [phi, lmat, cmat, Matrix.add_apply, Nm]
  ring

theorem phi_mulVec (c : E) (w : E × E) (u : E) :
    D.phi c w *ᵥ ![D.X u, D.Y u] =
      ![D.X (w.1 * u + c * w.2 * D.bar u), D.Y (w.1 * u + c * w.2 * D.bar u)] := by
  rw [phi, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, D.cmat_mulVec, D.lmat_mulVec,
    D.lmat_mulVec]
  ext i
  fin_cases i <;> simp [D.X_add, D.Y_add]

theorem phi_injective {c : E} (hc : c ≠ 0) : Function.Injective (D.phi c) := by
  have hadd : ∀ w w' : E × E, D.phi c w = D.phi c w' → w = w' := by
    intro w w' h
    have h0 : D.phi c (w - w') = 0 := by
      have := D.phi_add c (w - w') w'
      rw [sub_add_cancel, h] at this
      simpa using this
    set v := w - w' with hv
    have hu : ∀ u : E, v.1 * u + c * v.2 * D.bar u = 0 := by
      intro u
      have h1 := D.phi_mulVec c v u
      rw [h0, Matrix.zero_mulVec] at h1
      refine D.ext_coords ?_ ?_
      · simpa [X] using (congrFun h1 0).symm
      · simpa [Y] using (congrFun h1 1).symm
    have h1 := hu 1
    have h2 := hu D.ω
    rw [map_one, mul_one, mul_one] at h1
    have h3 : c * v.2 * (D.bar D.ω - D.ω) = 0 := by linear_combination h2 - D.ω * h1
    have hv2 : v.2 = 0 := by
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact (mul_eq_zero.mp h4).resolve_left hc
      · exact absurd (sub_eq_zero.mp h4) D.bar_ne
    have hv1 : v.1 = 0 := by
      rw [hv2, mul_zero, add_zero] at h1
      exact h1
    exact sub_eq_zero.mp (Prod.ext hv1 hv2)
  exact hadd

include D in
theorem finrank_eq_two : finrank K E = 2 := by
  rw [Module.finrank_eq_card_basis D.basis]
  simp

@[expose] noncomputable def phiEquiv {c : E} (hc : c ≠ 0) :
    (E × E) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  haveI : Module.Finite K E := Module.Finite.of_basis D.basis
  LinearEquiv.ofInjectiveOfFinrankEq (D.phiL c) (D.phi_injective hc) (by
    rw [Module.finrank_prod, D.finrank_eq_two, Module.finrank_matrix]
    simp)

theorem phiEquiv_apply {c : E} (hc : c ≠ 0) (w : E × E) : D.phiEquiv hc w = D.phi c w := rfl

theorem lmat_mul_phi (c lam : E) (w : E × E) :
    D.lmat lam * D.phi c w = D.phi c (lam * w.1, lam * w.2) := by
  simp only [phi, Matrix.mul_add, ← Matrix.mul_assoc, ← D.lmat_mul]
  congr 3
  ring

theorem phi_mul_lmat (c eta : E) (w : E × E) :
    D.phi c w * D.lmat eta = D.phi c (eta * w.1, D.bar eta * w.2) := by
  unfold phi
  rw [Matrix.add_mul, Matrix.mul_assoc, D.cmat_mul_lmat, ← Matrix.mul_assoc, ← D.lmat_mul,
    ← D.lmat_mul]
  have e1 : w.1 * eta = eta * w.1 := mul_comm _ _
  have e2 : c * w.2 * D.bar eta = c * (D.bar eta * w.2) := by ring
  rw [e1, e2]

theorem cmat_mul_phi_mul_cmat (w : E × E) :
    D.cmat * D.phi 1 w * D.cmat = D.phi 1 (D.bar w.1, D.bar w.2) := by
  have h1 := D.cmat_mul_lmat w.1
  have h2 := D.cmat_mul_lmat w.2
  have h3 := D.cmat_mul_cmat
  unfold phi
  simp only [one_mul]
  calc D.cmat * (D.lmat w.1 + D.lmat w.2 * D.cmat) * D.cmat
      = (D.cmat * D.lmat w.1) * D.cmat + (D.cmat * D.lmat w.2) * (D.cmat * D.cmat) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = D.lmat (D.bar w.1) + D.lmat (D.bar w.2) * D.cmat := by
        rw [h1, h2, h3, Matrix.mul_one, Matrix.mul_assoc, h3, Matrix.mul_one]

theorem lmat_cmat_phi {c : E} (hc : c ≠ 0) (w : E × E) :
    (D.lmat c * D.cmat) * D.phi c w * (D.cmat * D.lmat c⁻¹) =
      D.phi c (D.bar w.1, D.bar w.2) := by
  have h1 := D.cmat_mul_lmat w.1
  have h3 := D.cmat_mul_cmat
  have hcc : D.lmat c * D.lmat c⁻¹ = 1 := by rw [← D.lmat_mul, mul_inv_cancel₀ hc, D.lmat_one]
  unfold phi
  have e1 : D.lmat c * D.cmat * D.lmat w.1 * (D.cmat * D.lmat c⁻¹) = D.lmat (D.bar w.1) := by
    calc D.lmat c * D.cmat * D.lmat w.1 * (D.cmat * D.lmat c⁻¹)
        = D.lmat c * ((D.cmat * D.lmat w.1) * D.cmat) * D.lmat c⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = D.lmat c * D.lmat (D.bar w.1) * D.lmat c⁻¹ := by
          rw [h1, Matrix.mul_assoc _ D.cmat D.cmat, h3, Matrix.mul_one]
      _ = D.lmat (D.bar w.1) := by
          rw [← D.lmat_mul, ← D.lmat_mul]
          congr 1
          field_simp
  have e2 : D.lmat c * D.cmat * (D.lmat (c * w.2) * D.cmat) * (D.cmat * D.lmat c⁻¹) =
      D.lmat (c * D.bar w.2) * D.cmat := by
    have hb : D.cmat * D.lmat (c * w.2) = D.lmat (D.bar c * D.bar w.2) * D.cmat := by
      rw [D.cmat_mul_lmat, map_mul]
    have hb' : D.cmat * D.lmat c⁻¹ = D.lmat (D.bar c)⁻¹ * D.cmat := by
      rw [D.cmat_mul_lmat, map_inv₀]
    calc D.lmat c * D.cmat * (D.lmat (c * w.2) * D.cmat) * (D.cmat * D.lmat c⁻¹)
        = D.lmat c * (D.cmat * D.lmat (c * w.2)) * (D.cmat * D.cmat) * D.lmat c⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = D.lmat c * (D.lmat (D.bar c * D.bar w.2) * D.cmat) * D.lmat c⁻¹ := by
          rw [hb, h3, Matrix.mul_one]
      _ = D.lmat c * D.lmat (D.bar c * D.bar w.2) * (D.cmat * D.lmat c⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = D.lmat c * D.lmat (D.bar c * D.bar w.2) * (D.lmat (D.bar c)⁻¹ * D.cmat) := by
          rw [hb']
      _ = D.lmat (c * (D.bar c * D.bar w.2) * (D.bar c)⁻¹) * D.cmat := by
          rw [← Matrix.mul_assoc, ← D.lmat_mul, ← D.lmat_mul]
      _ = D.lmat (c * D.bar w.2) * D.cmat := by
          congr 2
          have : D.bar c ≠ 0 := fun h0 => hc (by simpa using h0)
          field_simp
  calc D.lmat c * D.cmat * (D.lmat w.1 + D.lmat (c * w.2) * D.cmat) * (D.cmat * D.lmat c⁻¹)
      = D.lmat c * D.cmat * D.lmat w.1 * (D.cmat * D.lmat c⁻¹) +
        D.lmat c * D.cmat * (D.lmat (c * w.2) * D.cmat) * (D.cmat * D.lmat c⁻¹) := by
        simp only [Matrix.mul_add, Matrix.add_mul]
    _ = _ := by rw [e1, e2]

theorem phi_neg (c : E) (w : E × E) : D.phi c (-w) = -D.phi c w := by
  have := D.phi_smul c (-1 : K) w
  simpa using this

theorem lmatC_mul_inv {c : E} (hc : c ≠ 0) :
    (D.lmat c * D.cmat) * (D.cmat * D.lmat c⁻¹) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc D.cmat D.cmat, D.cmat_mul_cmat, Matrix.one_mul,
    ← D.lmat_mul, mul_inv_cancel₀ hc, D.lmat_one]

theorem lmatC_det {c : E} (hNc : D.Nm c = -1) : (D.lmat c * D.cmat).det = 1 := by
  rw [Matrix.det_mul, D.lmat_det, hNc, D.cmat_det]
  ring

theorem lmat_det_eq_one {lam : E} (h : lam * D.bar lam = 1) : (D.lmat lam).det = 1 := by
  rw [D.lmat_det]
  refine (algebraMap K E).injective ?_
  rw [D.algebraMap_Nm, h, map_one]

end QuadData

section Finite

variable {K E : Type*} [Field K] [Finite K] [Field E] [Algebra K E]

theorem exists_quadData (hE : finrank K E = 2) :
    ∃ D : QuadData K E, ∀ z, D.bar z = z ^ Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Module.Finite K E := Module.finite_of_finrank_pos (by omega)
  have : Finite E := Module.finite_of_finite K
  have hGal : IsGalois K E := inferInstance
  have : Fintype E := Fintype.ofFinite E
  set bar : E ≃ₐ[K] E := FiniteField.frobeniusAlgEquivOfAlgebraic K E with hbar
  have hbar_apply : ∀ z, bar z = z ^ Nat.card K := fun z => by
    rw [Nat.card_eq_fintype_card, hbar, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  have hbar_bar : ∀ z, bar (bar z) = z := fun z => by
    rw [hbar_apply, hbar_apply, ← pow_mul, Nat.card_eq_fintype_card]
    have hcard : Fintype.card K * Fintype.card K = Fintype.card E := by
      rw [Module.card_eq_pow_finrank (K := K) (V := E), hE, sq]
    rw [hcard]
    exact FiniteField.pow_card z
  have hne : ∃ z : E, bar z ≠ z := by
    by_contra hcon
    push Not at hcon
    have h1 : FiniteField.frobeniusAlgHom K E = 1 := AlgHom.ext fun z => by
      rw [FiniteField.frobeniusAlgHom_apply, ← Nat.card_eq_fintype_card, ← hbar_apply]
      exact hcon z
    have h2 := FiniteField.orderOf_frobeniusAlgHom K E
    rw [h1, orderOf_one, hE] at h2
    omega
  have hfix : ∀ z : E, bar z = z → ∃ x : K, algebraMap K E x = z := by
    intro z hz
    have hmem : z ∈ (⊥ : IntermediateField K E) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro g
      have hsurj := (FiniteField.bijective_frobeniusAlgHom_pow (K := K) (L := E)).2 g.toAlgHom
      obtain ⟨n, hn⟩ := hsurj
      have hpow : ∀ m : ℕ, ((FiniteField.frobeniusAlgHom K E) ^ m) z = z := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          rw [pow_succ, AlgHom.mul_apply, FiniteField.frobeniusAlgHom_apply,
            ← Nat.card_eq_fintype_card, ← hbar_apply, hz, ih]
      have := congrArg (fun f : E →ₐ[K] E => f z) hn
      simpa [hpow] using this.symm
    exact IntermediateField.mem_bot.mp hmem
  obtain ⟨ω, hω⟩ := hne
  obtain ⟨t, ht⟩ := hfix (ω + bar ω) (by rw [map_add, hbar_bar, add_comm])
  obtain ⟨n, hn⟩ := hfix (ω * bar ω) (by rw [map_mul, hbar_bar, mul_comm])
  have hli : LinearIndependent K ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s r hsr
    have hsr' : algebraMap K E s + algebraMap K E r * ω = 0 := by
      simpa [Algebra.smul_def] using hsr
    by_cases hr : r = 0
    · subst hr
      refine ⟨?_, rfl⟩
      simpa using hsr'
    · exfalso
      apply hω
      have : ω = algebraMap K E (-(s / r)) := by
        have hr' : algebraMap K E r ≠ 0 := by simpa using hr
        rw [map_neg, map_div₀]
        field_simp
        linear_combination hsr'
      rw [this, AlgEquiv.commutes]
  have hcardE : Fintype.card (Fin 2) = finrank K E := by simp [hE]
  refine ⟨⟨bar, hbar_bar, ω, t, n, basisOfLinearIndependentOfCardEqFinrank hli hcardE, ?_, ?_, ?_,
    ?_, hω⟩, hbar_apply⟩
  · simp
  · simp
  · rw [ht]; ring
  · rw [ht, hn]
    ring

end Finite

end CFSG.RankThree.PartOne.KCOrthogonal
