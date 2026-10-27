module

public import CFSG.RankThree.PartOne.KF.K0Eigen
public import CFSG.RankThree.PartOne.KF.K0SU3Form

public section

namespace CFSG.RankThree.PartOne.KFK0

open Matrix CFSG.LieType.Universal.Unitary Polynomial

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem smat_pow (u : ↥(SU σ 3)) (n : ℕ) : smat (u ^ n) = smat u ^ n := by
  induction n with
  | zero => simp [smat_one]
  | succ n ih => rw [pow_succ, smat_mul, ih, pow_succ]

theorem hf_left_eigen (u : ↥(SU σ 3)) {v : Fin 3 → K} {l : K} (hl : l ≠ 0) (hσl : σ l = l)
    (hv : smat u *ᵥ v = l • v) (z : Fin 3 → K) : hf σ v (smat u *ᵥ z) = l⁻¹ * hf σ v z := by
  have h1 : smat u *ᵥ (l⁻¹ • v) = v := by
    rw [Matrix.mulVec_smul, hv, smul_smul, inv_mul_cancel₀ hl, one_smul]
  calc hf σ v (smat u *ᵥ z) = hf σ (smat u *ᵥ (l⁻¹ • v)) (smat u *ᵥ z) := by rw [h1]
    _ = hf σ (l⁻¹ • v) z := hf_mulVec_SU u _ _
    _ = l⁻¹ * hf σ v z := by rw [hf_smul_left, map_inv₀, hσl]

theorem hf_self_eq_zero_of_eigen (u : ↥(SU σ 3)) {y : Fin 3 → K} {μ : K} (hσμ : σ μ = μ)
    (hμ2 : μ ^ 2 ≠ 1) (hy : smat u *ᵥ y = μ • y) : hf σ y y = 0 := by
  have h := hf_mulVec_SU u y y
  rw [hy, hf_smul_left, hf_smul_right, hσμ] at h
  have : (μ ^ 2 - 1) * hf σ y y = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hμ2)

theorem hf_aeval_mulVec (u : ↥(SU σ 3)) {v : Fin 3 → K} {c : K}
    (hc : ∀ z, hf σ v (smat u *ᵥ z) = c * hf σ v z) (P : K[X]) (y : Fin 3 → K) :
    hf σ v ((Polynomial.aeval (smat u) P) *ᵥ y) = P.eval c * hf σ v y := by
  have hpow : ∀ (n : ℕ) (z : Fin 3 → K), hf σ v (smat u ^ n *ᵥ z) = c ^ n * hf σ v z := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, ← Matrix.mulVec_mulVec, ih, hc]
      ring
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, Matrix.add_mulVec, hf_add_right, hP, hQ, eval_add, add_mul]
  | monomial n a =>
    rw [aeval_monomial, eval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec, show a • (smat u ^ n *ᵥ y) = a • (smat u ^ n *ᵥ y) from rfl]
    rw [show hf σ v (a • (smat u ^ n *ᵥ y)) = a * hf σ v (smat u ^ n *ᵥ y) from hf_smul_right a _ _,
      hpow]
    ring

theorem eq_one_of_sq_of_pow {p : ℕ} (hpodd : Odd p) {b : K} (h2 : b ^ 2 = 1) (hp : b ^ p = 1) :
    b = 1 := by
  obtain ⟨k, hk⟩ := hpodd
  have h3 : b ^ p = b := by rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul]
  exact h3.symm.trans hp

theorem sq_ne_one_of_ne_one {p : ℕ} (hpodd : Odd p) {b : K} (hp : b ^ p = 1) (h1 : b ≠ 1) :
    b ^ 2 ≠ 1 := fun h2 => h1 (eq_one_of_sq_of_pow hpodd h2 hp)

theorem exists_coords {v x w : Fin 3 → K} (hli : LinearIndependent K ![v, x, w]) (y : Fin 3 → K) :
    ∃ a b c : K, y = a • v + b • x + c • w := by
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hy : y ∈ Submodule.span K (Set.range ![v, x, w]) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
  exact ⟨c 0, c 1, c 2, by rw [← hc]; simp [Fin.sum_univ_three]⟩

theorem eq_zero_of_lin_comb {v x w : Fin 3 → K} (hli : LinearIndependent K ![v, x, w])
    {a b c : K} (h : a • v + b • x + c • w = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have := Fintype.linearIndependent_iff.1 hli ![a, b, c] (by simpa [Fin.sum_univ_three] using h)
  exact ⟨this 0, this 1, this 2⟩

theorem exists_eigenbasis (hσ : ∀ c, σ (σ c) = c) {p : ℕ} (hp : 0 < p) (hpodd : Odd p) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hfix : ∀ ν : K, ν ^ p = 1 → σ ν = ν) {u : ↥(SU σ 3)}
    (hu : u ^ p = 1) (hu1 : u ≠ 1) :
    ∃ (l : K) (v w x : Fin 3 → K), l ^ p = 1 ∧ l ≠ 1 ∧ smat u *ᵥ v = l • v ∧
      smat u *ᵥ w = l⁻¹ • w ∧ smat u *ᵥ x = x ∧ hf σ v v = 0 ∧ hf σ w w = 0 ∧ hf σ x x ≠ 0 ∧
      LinearIndependent K ![v, x, w] := by
  classical
  have hUp : smat u ^ p = 1 := by rw [← smat_pow, hu, smat_one]
  have hU1 : smat u ≠ 1 := fun h => hu1 (Subtype.ext (Units.ext (by simpa [smat] using h)))
  obtain ⟨l, hlp, hl1, v, hv0, hv⟩ := exists_eigenvector_of_pow_eq_one hp hζ hUp hU1
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hlp
    exact zero_ne_one hlp
  have hlsq : l ^ 2 ≠ 1 := sq_ne_one_of_ne_one hpodd hlp hl1
  have hσl : σ l = l := hfix l hlp
  have hσli : σ l⁻¹ = l⁻¹ := by rw [map_inv₀, hσl]
  have hlip : (l⁻¹) ^ p = 1 := by rw [inv_pow, hlp, inv_one]
  have hlisq : (l⁻¹) ^ 2 ≠ 1 := by
    rw [inv_pow]
    exact fun h => hlsq (inv_eq_one.1 h)
  have hvv : hf σ v v = 0 := hf_self_eq_zero_of_eigen u hσl hlsq hv
  obtain ⟨w', hw'⟩ : ∃ w', hf σ v w' ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (eq_zero_of_hf_right σ.injective h)
  set Q := Polynomial.aeval (smat u) (projPoly p l⁻¹) with hQ
  set w := Q *ᵥ w' with hw
  have hUw : smat u *ᵥ w = l⁻¹ • w := by
    have h0 := sub_mul_aeval_projPoly hp hζ hlip hUp
    rw [← hQ, sub_mul, smul_mul_assoc, one_mul, sub_eq_zero] at h0
    rw [hw, Matrix.mulVec_mulVec, h0, Matrix.smul_mulVec]
  have hvw : hf σ v w ≠ 0 := by
    have h1 := hf_aeval_mulVec u (v := v) (c := l⁻¹) (hf_left_eigen u hl0 hσl hv) (projPoly p l⁻¹) w'
    rw [← hQ, ← hw] at h1
    rw [h1]
    refine mul_ne_zero ?_ hw'
    simp only [projPoly, eval_prod, eval_sub, eval_X, eval_C]
    refine Finset.prod_ne_zero_iff.2 fun ν hν => ?_
    exact sub_ne_zero.2 (Ne.symm (Finset.mem_erase.1 hν).1)
  have hww : hf σ w w = 0 := hf_self_eq_zero_of_eigen u hσli hlisq hUw
  have hw0 : w ≠ 0 := fun h => hvw (by rw [h, hf_zero_right])
  let T : (Fin 3 → K) →ₗ[K] (Fin 2 → K) :=
    { toFun := fun z => ![hf σ v z, hf σ w z]
      map_add' := by
        intro a b
        ext i
        fin_cases i <;> simp [hf_add_right]
      map_smul' := by
        intro c a
        ext i
        fin_cases i <;> simp [hf_smul_right] }
  have hker : LinearMap.ker T ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨x, hxker, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hTx : ![hf σ v x, hf σ w x] = (0 : Fin 2 → K) := hxker
  have hvx : hf σ v x = 0 := by simpa using congrFun hTx 0
  have hwx : hf σ w x = 0 := by simpa using congrFun hTx 1
  have hxv : hf σ x v = 0 := by rw [hf_comm hσ, hvx, map_zero]
  have hxw : hf σ x w = 0 := by rw [hf_comm hσ, hwx, map_zero]
  have hwv : hf σ w v = σ (hf σ v w) := hf_comm hσ v w
  have hwv0 : hf σ w v ≠ 0 := by rw [hwv]; exact (map_ne_zero_iff σ σ.injective).2 hvw
  have hli : LinearIndependent K ![v, x, w] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • v + g 1 • x + g 2 • w = 0 := by simpa [Fin.sum_univ_three] using hg
    have e1 := congrArg (hf σ v) hg'
    rw [hf_add_right, hf_add_right, hf_smul_right, hf_smul_right, hf_smul_right, hvv, hvx,
      hf_zero_right] at e1
    have hg2 : g 2 = 0 := by
      have : g 2 * hf σ v w = 0 := by linear_combination e1
      exact (mul_eq_zero.1 this).resolve_right hvw
    have e2 := congrArg (hf σ w) hg'
    rw [hf_add_right, hf_add_right, hf_smul_right, hf_smul_right, hf_smul_right, hww, hwx,
      hf_zero_right] at e2
    have hg0 : g 0 = 0 := by
      have : g 0 * hf σ w v = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_right hwv0
    rw [hg0, hg2, zero_smul, zero_smul, zero_add, add_zero] at hg'
    have hg1 : g 1 = 0 := (smul_eq_zero.1 hg').resolve_right hx0
    intro i
    fin_cases i <;> simp [hg0, hg1, hg2]
  have hxx : hf σ x x ≠ 0 := by
    intro h0
    apply hx0
    apply eq_zero_of_hf_right σ.injective
    intro z
    obtain ⟨a, b, c, rfl⟩ := exists_coords hli z
    rw [hf_add_right, hf_add_right, hf_smul_right, hf_smul_right, hf_smul_right, h0, hxv, hxw]
    ring
  have hUx : smat u *ᵥ x = x := by
    obtain ⟨a, b, c, hab⟩ := exists_coords hli (smat u *ᵥ x)
    have e1 : hf σ v (smat u *ᵥ x) = 0 := by
      rw [hf_left_eigen u hl0 hσl hv, hvx, mul_zero]
    have e2 : hf σ w (smat u *ᵥ x) = 0 := by
      rw [hf_left_eigen u (inv_ne_zero hl0) hσli hUw, hwx, mul_zero]
    rw [hab, hf_add_right, hf_add_right, hf_smul_right, hf_smul_right, hf_smul_right, hvv, hvx] at e1
    rw [hab, hf_add_right, hf_add_right, hf_smul_right, hf_smul_right, hf_smul_right, hww, hwx] at e2
    have hc : c = 0 := by
      have : c * hf σ v w = 0 := by linear_combination e1
      exact (mul_eq_zero.1 this).resolve_right hvw
    have ha : a = 0 := by
      have : a * hf σ w v = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_right hwv0
    rw [ha, hc, zero_smul, zero_smul, zero_add, add_zero] at hab
    have hpowb : ∀ n : ℕ, smat u ^ n *ᵥ x = b ^ n • x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hab, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
        ring_nf
    have hbp : b ^ p = 1 := by
      have h1 := hpowb p
      rw [hUp, Matrix.one_mulVec] at h1
      have h2 : (b ^ p - 1) • x = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hx0)
    have hσb : σ b = b := hfix b hbp
    have hb2 : b ^ 2 = 1 := by
      have h := hf_mulVec_SU u x x
      rw [hab, hf_smul_left, hf_smul_right, hσb] at h
      have : (b ^ 2 - 1) * hf σ x x = 0 := by linear_combination h
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hxx)
    rw [hab, eq_one_of_sq_of_pow hpodd hb2 hbp, one_smul]
  exact ⟨l, v, w, x, hlp, hl1, hv, hUw, hUx, hvv, hww, hxx, hli⟩

theorem eigen_isotropic_cases {u : ↥(SU σ 3)} {l : K} {v w x : Fin 3 → K}
    (hli : LinearIndependent K ![v, x, w]) (hl1 : l ≠ 1) (hli1 : l⁻¹ ≠ 1) (hll : l ≠ l⁻¹)
    (hxx : hf σ x x ≠ 0) (hUv : smat u *ᵥ v = l • v) (hUw : smat u *ᵥ w = l⁻¹ • w)
    (hUx : smat u *ᵥ x = x) {y : Fin 3 → K} (hy0 : y ≠ 0) {μ : K} (hUy : smat u *ᵥ y = μ • y)
    (hyy : hf σ y y = 0) : (∃ c : K, c ≠ 0 ∧ y = c • v) ∨ ∃ c : K, c ≠ 0 ∧ y = c • w := by
  obtain ⟨a, b, c, rfl⟩ := exists_coords hli y
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_smul, hUv, hUw, hUx] at hUy
  have hcomb : (a * l - μ * a) • v + (b - μ * b) • x + (c * l⁻¹ - μ * c) • w = 0 := by
    have : (a * l - μ * a) • v + (b - μ * b) • x + (c * l⁻¹ - μ * c) • w =
        (a • l • v + b • x + c • l⁻¹ • w) - μ • (a • v + b • x + c • w) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [this, hUy, sub_self]
  obtain ⟨h1, h2, h3⟩ := eq_zero_of_lin_comb hli hcomb
  have hb : b = 0 := by
    by_contra hb
    have hμ : μ = 1 := by
      have : (1 - μ) * b = 0 := by linear_combination h2
      exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hb)).symm
    subst hμ
    have ha : a = 0 := by
      have : a * (l - 1) = 0 := by linear_combination h1
      exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hl1)
    have hc : c = 0 := by
      have : c * (l⁻¹ - 1) = 0 := by linear_combination h3
      exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hli1)
    rw [ha, hc, zero_smul, zero_smul, zero_add, add_zero, hf_smul_left, hf_smul_right] at hyy
    have : σ b * (b * hf σ x x) = 0 := hyy
    rcases mul_eq_zero.1 this with h | h
    · exact hb (σ.injective (by rw [h, map_zero]))
    · exact (mul_eq_zero.1 h).elim hb hxx
  subst hb
  rw [zero_smul, add_zero] at *
  by_cases ha : a = 0
  · subst ha
    rw [zero_smul, zero_add] at *
    right
    refine ⟨c, fun hc => hy0 (by rw [hc, zero_smul]), rfl⟩
  · by_cases hc : c = 0
    · subst hc
      left
      exact ⟨a, ha, by rw [zero_smul, add_zero]⟩
    · exfalso
      have hμl : μ = l := by
        have : (l - μ) * a = 0 := by linear_combination h1
        exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right ha)).symm
      have hμl' : μ = l⁻¹ := by
        have : (l⁻¹ - μ) * c = 0 := by linear_combination h3
        exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hc)).symm
      exact hll (hμl.symm.trans hμl')

end CFSG.RankThree.PartOne.KFK0
