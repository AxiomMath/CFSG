module

public import CFSG.RankThree.GF2n.Smith81.TiD3Model

public section

namespace CFSG.RankThree.GF2n.Smith81.D3

open Matrix
open scoped MatrixGroups

section Basic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

@[expose] def e1 (F : Type*) [Field F] : Hyp F := fun i j k =>
  if i = 1 ∧ j = 1 ∧ k = 1 then 1 else 0

@[expose] def embP (τ : F →ₐ[K] F) (p : F) : Hyp F := fun i j k =>
  if i = 0 ∧ j = 0 ∧ k = 1 then p
  else if i = 1 ∧ j = 0 ∧ k = 0 then τ p
  else if i = 0 ∧ j = 1 ∧ k = 0 then τ (τ p)
  else 0

@[expose] def embR (τ : F →ₐ[K] F) (r : F) : Hyp F := fun i j k =>
  if i = 0 ∧ j = 1 ∧ k = 1 then r
  else if i = 1 ∧ j = 0 ∧ k = 1 then τ r
  else if i = 1 ∧ j = 1 ∧ k = 0 then τ (τ r)
  else 0

@[expose] def tr3 (τ : F →ₐ[K] F) (x : F) : F := x + τ x + τ (τ x)

@[expose] def nrm3 (τ : F →ₐ[K] F) (x : F) : F := x * τ x * τ (τ x)

theorem e0_mem_kForm (τ : F →ₐ[K] F) : e0 F ∈ kForm τ := by
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [e0]

theorem e1_mem_kForm (τ : F →ₐ[K] F) : e1 F ∈ kForm τ := by
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [e1]

theorem embP_mem_kForm (τ : F →ₐ[K] F) (hτ : ∀ a, τ (τ (τ a)) = a) (p : F) :
    embP τ p ∈ kForm τ := by
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [embP, hτ]

theorem embR_mem_kForm (τ : F →ₐ[K] F) (hτ : ∀ a, τ (τ (τ a)) = a) (r : F) :
    embR τ r ∈ kForm τ := by
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [embR, hτ]

theorem tau_cube [Fintype K] [Fintype F] (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ Fintype.card K)
    (hF : Fintype.card F = Fintype.card K ^ 3) (a : F) : τ (τ (τ a)) = a := by
  have h3 : Fintype.card K * (Fintype.card K * Fintype.card K) = Fintype.card F := by
    rw [hF]; ring
  rw [hτ, hτ, hτ, ← pow_mul, ← pow_mul, h3]
  exact FiniteField.pow_card a

theorem fix_mem_range [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (x : F) (hx : τ x = x) :
    ∃ c : K, algebraMap K F c = x := by
  have h : x ^ Fintype.card K = x := by rw [← hτ, hx]
  exact (pow_card_eq_self_iff x).mp h

theorem nrm3_mem_range [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hτ3 : ∀ a, τ (τ (τ a)) = a) (x : F) :
    ∃ c : K, algebraMap K F c = nrm3 τ x := by
  apply fix_mem_range τ hτ
  simp only [nrm3, map_mul, hτ3]
  ring

theorem nrm3_eq_pow [Fintype K] (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ Fintype.card K) (μ : F) :
    nrm3 τ μ = μ ^ (1 + Fintype.card K + Fintype.card K ^ 2) := by
  simp only [nrm3, hτ]
  ring

@[expose] def vE0 (τ : F →ₐ[K] F) : kForm τ := ⟨e0 F, e0_mem_kForm τ⟩

@[expose] def vE1 (τ : F →ₐ[K] F) : kForm τ := ⟨e1 F, e1_mem_kForm τ⟩

@[expose] def vP (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (p : F) : kForm τ :=
  ⟨embP τ p, embP_mem_kForm τ hτ3 p⟩

@[expose] def vR (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (r : F) : kForm τ :=
  ⟨embR τ r, embR_mem_kForm τ hτ3 r⟩

@[expose] def vPt (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (w : Fin 2 → F) : kForm τ :=
  ⟨pt (τ : F →+* F) w, pt_mem_kForm τ hτ3 w⟩

theorem kForm_decomp [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hτ3 : ∀ a, τ (τ (τ a)) = a) (x : kForm τ) :
    ∃ c0 c1 : K, x = c0 • vE0 τ + c1 • vE1 τ + vP τ hτ3 ((x : Hyp F) 0 0 1) +
      vR τ hτ3 ((x : Hyp F) 0 1 1) := by
  have hx : ∀ i j k, (x : Hyp F) k i j = τ ((x : Hyp F) i j k) := fun i j k => x.2 i j k
  have h100 : (x : Hyp F) 1 0 0 = τ ((x : Hyp F) 0 0 1) := hx 0 0 1
  have h010 : (x : Hyp F) 0 1 0 = τ (τ ((x : Hyp F) 0 0 1)) := by
    rw [hx 1 0 0, h100]
  have h101 : (x : Hyp F) 1 0 1 = τ ((x : Hyp F) 0 1 1) := hx 0 1 1
  have h110 : (x : Hyp F) 1 1 0 = τ (τ ((x : Hyp F) 0 1 1)) := by
    rw [hx 1 0 1, h101]
  obtain ⟨c0, hc0⟩ := fix_mem_range τ hτ ((x : Hyp F) 0 0 0) (hx 0 0 0).symm
  obtain ⟨c1, hc1⟩ := fix_mem_range τ hτ ((x : Hyp F) 1 1 1) (hx 1 1 1).symm
  refine ⟨c0, c1, Subtype.ext ?_⟩
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [vE0, vE1, vP, vR, e0, e1, embP, embR, Algebra.smul_def, hc0, hc1, h100, h010, h101,
      h110, hτ3]

theorem quad_e0 : quad (e0 F) = 0 := by
  simp [quad, e0]

theorem quad_e1 : quad (e1 F) = 0 := by
  simp [quad, e1]

theorem exists_sl_mulVec_pi_single {w : Fin 2 → F} (hw : w ≠ 0) :
    ∃ g : SL(2, F), (g : Mat2 F) *ᵥ Pi.single 0 1 = w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      apply hw
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![0, -(w 1)⁻¹; w 1, 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simp [h1]
    · funext i
      fin_cases i <;> simp [h0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
  · refine ⟨⟨!![w 0, 0; w 1, (w 0)⁻¹], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simp [h0]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply, h0]

theorem act_add (τ : F →+* F) (g : Mat2 F) (x y : Hyp F) :
    act τ g (x + y) = act τ g x + act τ g y := by
  funext i j k
  simp only [act, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem vPt_smul [Fintype K] [Fintype F] (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ Fintype.card K)
    (hτ3 : ∀ a, τ (τ (τ a)) = a) (s : F) (v : Fin 2 → F) :
    ∃ k : K, algebraMap K F k = s * τ s * τ (τ s) ∧
      vPt τ hτ3 (s • v) = k • vPt τ hτ3 v := by
  obtain ⟨k, hk⟩ := nrm3_mem_range τ hτ hτ3 s
  have hk' : algebraMap K F k = s * τ s * τ (τ s) := hk
  refine ⟨k, hk', Subtype.ext ?_⟩
  show pt (τ : F →+* F) (s • v) = k • pt (τ : F →+* F) v
  rw [pt_smul, show s * (τ : F →+* F) s * (τ : F →+* F) ((τ : F →+* F) s) =
    algebraMap K F k from hk'.symm]
  funext i j k'
  simp [Algebra.smul_def]

theorem beta_act_invariant (τ : F →ₐ[K] F) (Q : kForm τ → K)
    (β : LinearMap.BilinForm K (kForm τ))
    (hQa : ∀ x y, Q (x + y) = Q x + Q y + β x y)
    (hQg : ∀ (g : SL(2, F)) (x y : kForm τ),
      (y : Hyp F) = act (τ : F →+* F) (g : Mat2 F) (x : Hyp F) → Q y = Q x)
    (g : SL(2, F)) (x y x' y' : kForm τ)
    (hx : (x' : Hyp F) = act (τ : F →+* F) (g : Mat2 F) (x : Hyp F))
    (hy : (y' : Hyp F) = act (τ : F →+* F) (g : Mat2 F) (y : Hyp F)) :
    β x' y' = β x y := by
  have h1 := hQg g x x' hx
  have h2 := hQg g y y' hy
  have h3 := hQg g (x + y) (x' + y') (by
    rw [Submodule.coe_add, Submodule.coe_add, hx, hy, act_add])
  have e1 := hQa x' y'
  have e2 := hQa x y
  linear_combination (-1 : K) * e1 + e2 + h3 - h1 - h2

theorem Q_vPt_eq_of_ne_zero (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (Q : kForm τ → K)
    (hQg : ∀ (g : SL(2, F)) (x y : kForm τ),
      (y : Hyp F) = act (τ : F →+* F) (g : Mat2 F) (x : Hyp F) → Q y = Q x)
    {w : Fin 2 → F} (hw : w ≠ 0) : Q (vPt τ hτ3 w) = Q (vPt τ hτ3 (Pi.single 0 1)) := by
  obtain ⟨g, hg⟩ := exists_sl_mulVec_pi_single hw
  refine hQg g (vPt τ hτ3 (Pi.single 0 1)) (vPt τ hτ3 w) ?_
  show pt (τ : F →+* F) w = act (τ : F →+* F) (g : Mat2 F) (pt (τ : F →+* F) (Pi.single 0 1))
  rw [act_pt, hg]

theorem Q_vPt_eq_zero [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hτ3 : ∀ a, τ (τ (τ a)) = a)
    (hF : Fintype.card F = Fintype.card K ^ 3) (hK : 4 ≤ Fintype.card K) (h2K : (2 : K) = 0)
    (Q : kForm τ → K) (hQs : ∀ (a : K) (x : kForm τ), Q (a • x) = a ^ 2 * Q x)
    (hQg : ∀ (g : SL(2, F)) (x y : kForm τ),
      (y : Hyp F) = act (τ : F →+* F) (g : Mat2 F) (x : Hyp F) → Q y = Q x)
    (w : Fin 2 → F) : Q (vPt τ hτ3 w) = 0 := by
  by_cases hw : w = 0
  · have h0 : vPt τ hτ3 w = 0 := Subtype.ext (by subst hw; funext i j k; simp [vPt, pt])
    have hQ0 : Q 0 = 0 := by simpa using hQs 0 0
    rw [h0, hQ0]
  obtain ⟨κ, hκ0, hκ1⟩ : ∃ κ : K, κ ≠ 0 ∧ κ ≠ 1 := by
    classical
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset K) ⊆ ({0, 1} : Finset K) := by
      intro κ _
      by_cases h0 : κ = 0
      · simp [h0]
      · simp [h κ h0]
    have hc := Finset.card_le_card hsub
    have h2' : 2 < Fintype.card K := by omega
    simp at hc
    omega
  obtain ⟨μ, hμ0, hμ⟩ := exists_nrm_eq hF (by omega) κ hκ0
  have hμ' : algebraMap K F κ = μ * τ μ * τ (τ μ) := by
    rw [hμ, nrm3_eq_pow τ hτ μ |>.symm]
    rfl
  obtain ⟨k, hk, hscal⟩ := vPt_smul τ hτ hτ3 μ (Pi.single 0 1)
  have hk1 : k ≠ 1 := by
    intro h
    apply hκ1
    apply (algebraMap K F).injective
    rw [hμ', ← hk, h, map_one]
  have hw' : μ • (Pi.single 0 1 : Fin 2 → F) ≠ 0 := by
    intro h
    apply hμ0
    have := congrFun h 0
    simpa using this
  have e1 := Q_vPt_eq_of_ne_zero τ hτ3 Q hQg hw'
  have e2 : Q (vPt τ hτ3 (μ • Pi.single 0 1)) = k ^ 2 * Q (vPt τ hτ3 (Pi.single 0 1)) := by
    rw [hscal, hQs]
  have hk2 : k ^ 2 ≠ 1 := by
    intro h
    have hsq : (k - 1) ^ 2 = 0 := by linear_combination h - k * h2K + h2K
    exact hk1 (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq))
  have hprod : (k ^ 2 - 1) * Q (vPt τ hτ3 (Pi.single 0 1)) = 0 := by
    linear_combination e1 - e2
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) hk2
  · rw [Q_vPt_eq_of_ne_zero τ hτ3 Q hQg hw]
    exact h

theorem smul_of_det_eq_zero (h2 : (2 : F) = 0) {v w : Fin 2 → F} (hv : v ≠ 0)
    (hd : v 0 * w 1 + v 1 * w 0 = 0) : ∃ s : F, w = s • v := by
  by_cases h0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    have hw0 : w 0 = 0 := by
      have h' : v 1 * w 0 = 0 := by
        rw [h0, zero_mul, zero_add] at hd
        exact hd
      exact (mul_eq_zero.mp h').resolve_left hv1
    refine ⟨w 1 / v 1, ?_⟩
    funext i
    fin_cases i
    · simp [h0, hw0]
    · simp [hv1]
  · refine ⟨w 0 / v 0, ?_⟩
    have e1 : w 1 = w 0 / v 0 * v 1 := by
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination hd - (v 1 * w 0) * h2
    funext i
    fin_cases i
    · simp [h0]
    · exact e1

theorem beta_self_zero (τ : F →ₐ[K] F) (Q : kForm τ → K) (β : LinearMap.BilinForm K (kForm τ))
    (hQs : ∀ (a : K) (x : kForm τ), Q (a • x) = a ^ 2 * Q x)
    (hQa : ∀ x y, Q (x + y) = Q x + Q y + β x y) (h2K : (2 : K) = 0) (x : kForm τ) :
    β x x = 0 := by
  have h := hQa x x
  rw [← two_smul K x, hQs, h2K] at h
  linear_combination (-1 : K) * h - Q x * h2K

theorem beta_pt_eq [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hτ3 : ∀ a, τ (τ (τ a)) = a) (h2 : (2 : F) = 0)
    (h2K : (2 : K) = 0) (Q : kForm τ → K) (β : LinearMap.BilinForm K (kForm τ))
    (hQs : ∀ (a : K) (x : kForm τ), Q (a • x) = a ^ 2 * Q x)
    (hQa : ∀ x y, Q (x + y) = Q x + Q y + β x y)
    (hQg : ∀ (g : SL(2, F)) (x y : kForm τ),
      (y : Hyp F) = act (τ : F →+* F) (g : Mat2 F) (x : Hyp F) → Q y = Q x)
    (v w : Fin 2 → F) :
    algebraMap K F (β (vPt τ hτ3 v) (vPt τ hτ3 w)) =
      algebraMap K F (β (vPt τ hτ3 (Pi.single 0 1)) (vPt τ hτ3 (Pi.single 1 1))) *
        polar (pt (τ : F →+* F) v) (pt (τ : F →+* F) w) := by
  rw [polar_pt]
  obtain ⟨d, hd⟩ : ∃ d : F, d = v 0 * w 1 + v 1 * w 0 := ⟨_, rfl⟩
  rw [← hd]
  by_cases hd0 : d = 0
  · have hβ0 : β (vPt τ hτ3 v) (vPt τ hτ3 w) = 0 := by
      by_cases hv : v = 0
      · subst hv
        have h0 : vPt τ hτ3 (0 : Fin 2 → F) = 0 :=
          Subtype.ext (by funext i j k; simp [vPt, pt])
        rw [h0]
        simp
      · obtain ⟨s, hs⟩ := smul_of_det_eq_zero h2 hv (hd.symm.trans hd0)
        obtain ⟨k, _, hk⟩ := vPt_smul τ hτ hτ3 s v
        rw [← hs] at hk
        rw [hk, map_smul, beta_self_zero τ Q β hQs hQa h2K, smul_zero]
    rw [hd0, hβ0]
    simp
  · have hdet : v 0 * w 1 - v 1 * w 0 = d := by
      rw [hd]
      linear_combination (-(v 1 * w 0)) * h2
    have hdinv : d⁻¹ * d = 1 := inv_mul_cancel₀ hd0
    obtain ⟨g, hg0, hg1⟩ : ∃ g : SL(2, F), (g : Mat2 F) *ᵥ Pi.single 0 1 = v ∧
        (g : Mat2 F) *ᵥ Pi.single 1 1 = d⁻¹ • w := by
      refine ⟨⟨!![v 0, d⁻¹ * w 0; v 1, d⁻¹ * w 1], ?_⟩, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        linear_combination d⁻¹ * hdet + hdinv
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
    have hx : ((vPt τ hτ3 v : kForm τ) : Hyp F) = act (τ : F →+* F) (g : Mat2 F)
        ((vPt τ hτ3 (Pi.single 0 1) : kForm τ) : Hyp F) := by
      show pt (τ : F →+* F) v = act (τ : F →+* F) (g : Mat2 F) (pt (τ : F →+* F) (Pi.single 0 1))
      rw [act_pt, hg0]
    have hy : ((vPt τ hτ3 (d⁻¹ • w) : kForm τ) : Hyp F) = act (τ : F →+* F) (g : Mat2 F)
        ((vPt τ hτ3 (Pi.single 1 1) : kForm τ) : Hyp F) := by
      show pt (τ : F →+* F) (d⁻¹ • w) = act (τ : F →+* F) (g : Mat2 F)
        (pt (τ : F →+* F) (Pi.single 1 1))
      rw [act_pt, hg1]
    have hβ1 : β (vPt τ hτ3 v) (vPt τ hτ3 (d⁻¹ • w)) =
        β (vPt τ hτ3 (Pi.single 0 1)) (vPt τ hτ3 (Pi.single 1 1)) :=
      beta_act_invariant τ Q β hQa hQg g _ _ _ _ hx hy
    obtain ⟨k, hk, hvk⟩ := vPt_smul τ hτ hτ3 d (d⁻¹ • w)
    have hk2 : algebraMap K F k = d * (τ : F →+* F) d * (τ : F →+* F) ((τ : F →+* F) d) := hk
    rw [smul_smul, mul_inv_cancel₀ hd0, one_smul] at hvk
    have hβ2 : β (vPt τ hτ3 v) (vPt τ hτ3 w) =
        k • β (vPt τ hτ3 (Pi.single 0 1)) (vPt τ hτ3 (Pi.single 1 1)) := by
      rw [hvk, map_smul, hβ1]
    rw [hβ2, smul_eq_mul, map_mul, hk2]
    ring

theorem tr3_add_tau_tau (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (h2 : (2 : F) = 0)
    (z : F) : tr3 τ (z + τ (τ z)) = 0 := by
  simp only [tr3, map_add, hτ3]
  linear_combination (z + τ z + τ (τ z)) * h2

theorem finrank_eq_three [Fintype K] [Fintype F] (hF : Fintype.card F = Fintype.card K ^ 3)
    (hK : 4 ≤ Fintype.card K) : Module.finrank K F = 3 := by
  have h := Module.card_eq_pow_finrank (K := K) (V := F)
  rw [hF] at h
  exact (Nat.pow_right_injective (by omega : 2 ≤ Fintype.card K) h).symm

theorem add_tau_tau_eq_zero_iff [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hτ3 : ∀ a, τ (τ (τ a)) = a) (h2 : (2 : F) = 0)
    (z : F) : z + τ (τ z) = 0 ↔ ∃ c : K, algebraMap K F c = z := by
  constructor
  · intro h
    have h1 : τ (τ z) = z := by linear_combination h - z * h2
    have h2' : τ z = z := by
      have := congrArg τ h1
      rw [hτ3] at this
      exact this.symm
    exact fix_mem_range τ hτ z h2'
  · rintro ⟨c, rfl⟩
    simp only [AlgHom.commutes]
    linear_combination (algebraMap K F c) * h2

theorem span_eq_top_of_tr [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hτ3 : ∀ a, τ (τ (τ a)) = a)
    (hF : Fintype.card F = Fintype.card K ^ 3) (hK : 4 ≤ Fintype.card K) (h2 : (2 : F) = 0)
    (X : Set F) (hX : ∀ z : F, z + τ (τ z) ∈ Submodule.span K X)
    {v : F} (hv : v ∈ X) (hvt : tr3 τ v ≠ 0) : Submodule.span K X = ⊤ := by
  let T : F →ₗ[K] F := LinearMap.id + (τ.toLinearMap ∘ₗ τ.toLinearMap)
  have hT : ∀ z, T z = z + τ (τ z) := fun z => rfl
  have hHS : LinearMap.range T ≤ Submodule.span K X := by
    rintro _ ⟨z, rfl⟩
    rw [hT]
    exact hX z
  have hvS : v ∈ Submodule.span K X := Submodule.subset_span hv
  have hHne : LinearMap.range T ≠ Submodule.span K X := by
    intro h
    have hvH : v ∈ LinearMap.range T := h ▸ hvS
    obtain ⟨z, hz⟩ := hvH
    apply hvt
    rw [← hz, hT]
    exact tr3_add_tau_tau τ hτ3 h2 z
  have hlt : LinearMap.range T < Submodule.span K X := lt_of_le_of_ne hHS hHne
  have hker : Module.finrank K (LinearMap.ker T) = 1 := by
    have hk : LinearMap.ker T = LinearMap.range (Algebra.linearMap K F) := by
      ext z
      rw [LinearMap.mem_ker, hT, LinearMap.mem_range, add_tau_tau_eq_zero_iff τ hτ hτ3 h2 z]
      simp [Algebra.linearMap_apply]
    rw [hk, LinearMap.finrank_range_of_inj (fun x y hxy => (algebraMap K F).injective hxy)]
    exact Module.finrank_self K
  have hfinR : Module.finrank K (LinearMap.range T) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker T
    rw [hker, finrank_eq_three hF hK] at h
    omega
  have hF3 := finrank_eq_three hF hK
  have hfinS := Submodule.finrank_lt_finrank_of_lt hlt
  have hle := Submodule.finrank_le (Submodule.span K X)
  rw [hfinR] at hfinS
  apply Submodule.eq_top_of_finrank_eq
  omega

theorem exists_tau_ne [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hF : Fintype.card F = Fintype.card K ^ 3)
    (hK : 4 ≤ Fintype.card K) : ∃ b : F, τ b ≠ b := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (algebraMap K F) := by
    intro y
    have hy : y ^ Fintype.card K = y := by rw [← hτ, h y]
    exact (pow_card_eq_self_iff y).mp hy
  have hc := Fintype.card_le_of_surjective (algebraMap K F) hsurj
  rw [hF] at hc
  have hlt3 : Fintype.card K ^ 1 < Fintype.card K ^ 3 :=
    Nat.pow_lt_pow_right (by omega) (by norm_num)
  rw [pow_one] at hlt3
  linarith

theorem tr3_mul_add (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (p b : F) :
    tr3 τ (p * τ (τ b) + b * τ (τ p)) = tr3 τ (p * (τ (τ b) + τ b)) := by
  simp only [tr3, map_add, map_mul, hτ3]
  ring

theorem embP_add (τ : F →ₐ[K] F) (p p' : F) : embP τ (p + p') = embP τ p + embP τ p' := by
  funext i j k
  simp only [embP, Pi.add_apply]
  split_ifs <;> simp [map_add]

theorem embR_add (τ : F →ₐ[K] F) (r r' : F) : embR τ (r + r') = embR τ r + embR τ r' := by
  funext i j k
  simp only [embR, Pi.add_apply]
  split_ifs <;> simp [map_add]

theorem embP_smul (τ : F →ₐ[K] F) (c : K) (p : F) : embP τ (c • p) = c • embP τ p := by
  funext i j k
  simp only [embP, Pi.smul_apply]
  split_ifs <;> simp [Algebra.smul_def]

theorem embR_smul (τ : F →ₐ[K] F) (c : K) (r : F) : embR τ (c • r) = c • embR τ r := by
  funext i j k
  simp only [embR, Pi.smul_apply]
  split_ifs <;> simp [Algebra.smul_def]

@[expose] def spPt (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) : Submodule K (kForm τ) :=
  Submodule.span K (Set.range (vPt τ hτ3))

theorem vE0_eq (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) :
    vE0 τ = vPt τ hτ3 (Pi.single 0 1) :=
  Subtype.ext (e0_eq_pt (τ : F →+* F))

theorem vE1_eq (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) :
    vE1 τ = vPt τ hτ3 (Pi.single 1 1) := by
  apply Subtype.ext
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [vE1, vPt, pt, e1, Pi.single_apply]

theorem vE0_mem (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) : vE0 τ ∈ spPt τ hτ3 := by
  rw [vE0_eq τ hτ3]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem vE1_mem (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) : vE1 τ ∈ spPt τ hτ3 := by
  rw [vE1_eq τ hτ3]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem pt_one_eq [Fintype K] [Fintype F] (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ Fintype.card K)
    (hτ3 : ∀ a, τ (τ (τ a)) = a) (p : F) :
    ∃ k : K, vPt τ hτ3 ![1, τ p] = vE0 τ + k • vE1 τ + vP τ hτ3 p +
      vR τ hτ3 (p * τ (τ p)) := by
  obtain ⟨k, hk⟩ := nrm3_mem_range τ hτ hτ3 p
  have hk' : algebraMap K F k = p * τ p * τ (τ p) := hk
  refine ⟨k, Subtype.ext ?_⟩
  funext i j k'
  fin_cases i <;> fin_cases j <;> fin_cases k' <;>
    simp [vPt, pt, vE0, vE1, vP, vR, e0, e1, embP, embR, Algebra.smul_def, hk', hτ3, map_mul] <;>
    ring

theorem vR_phi_mem [Fintype K] [Fintype F] (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ Fintype.card K)
    (hτ3 : ∀ a, τ (τ (τ a)) = a) (h2 : (2 : F) = 0) (p p' : F) :
    vR τ hτ3 (p * τ (τ p') + p' * τ (τ p)) ∈ spPt τ hτ3 := by
  obtain ⟨k1, hk1⟩ := nrm3_mem_range τ hτ hτ3 p
  obtain ⟨k2, hk2⟩ := nrm3_mem_range τ hτ hτ3 p'
  obtain ⟨k3, hk3⟩ := nrm3_mem_range τ hτ hτ3 (p + p')
  have hk1' : algebraMap K F k1 = p * τ p * τ (τ p) := hk1
  have hk2' : algebraMap K F k2 = p' * τ p' * τ (τ p') := hk2
  have hk3' : algebraMap K F k3 = (p + p') * τ (p + p') * τ (τ (p + p')) := hk3
  have h4 : (4 : F) = 0 := by linear_combination 2 * h2
  have key : vR τ hτ3 (p * τ (τ p') + p' * τ (τ p)) =
      vPt τ hτ3 ![1, τ p] + vPt τ hτ3 ![1, τ p'] + vPt τ hτ3 ![1, τ (p + p')] + vE0 τ +
        (k1 + k2 + k3) • vE1 τ := by
    apply Subtype.ext
    funext i j k'
    fin_cases i <;> fin_cases j <;> fin_cases k' <;>
      simp [vPt, pt, vE0, vE1, vR, e0, e1, embR, Algebra.smul_def, map_add, hk1', hk2', hk3',
        hτ3, map_mul, map_add] <;>
      ring_nf <;> simp [h2, h4]
  rw [key]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ ?_ ?_) ?_) (vE0_mem τ hτ3)) (Submodule.smul_mem _ _ (vE1_mem τ hτ3))
  · exact Submodule.subset_span ⟨_, rfl⟩
  · exact Submodule.subset_span ⟨_, rfl⟩
  · exact Submodule.subset_span ⟨_, rfl⟩

theorem vR_add (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (r r' : F) :
    vR τ hτ3 (r + r') = vR τ hτ3 r + vR τ hτ3 r' :=
  Subtype.ext (embR_add τ r r')

theorem vR_smul (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (c : K) (r : F) :
    vR τ hτ3 (c • r) = c • vR τ hτ3 r :=
  Subtype.ext (embR_smul τ c r)

theorem vR_zero (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) : vR τ hτ3 0 = 0 := by
  apply Subtype.ext
  funext i j k
  simp [vR, embR]

theorem vR_mem_spPt [Fintype K] [Fintype F] (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ Fintype.card K)
    (hτ3 : ∀ a, τ (τ (τ a)) = a) (hF : Fintype.card F = Fintype.card K ^ 3)
    (hK : 4 ≤ Fintype.card K) (h2 : (2 : F) = 0) (r : F) : vR τ hτ3 r ∈ spPt τ hτ3 := by
  let X2 : Set F := Set.range (fun pq : F × F => pq.1 * τ (τ pq.2) + pq.2 * τ (τ pq.1))
  let Z : Submodule K F :=
    { carrier := {r | vR τ hτ3 r ∈ spPt τ hτ3}
      add_mem' := fun {a b} ha hb => by
        show vR τ hτ3 (a + b) ∈ spPt τ hτ3
        rw [vR_add]
        exact Submodule.add_mem _ ha hb
      zero_mem' := by
        show vR τ hτ3 0 ∈ spPt τ hτ3
        rw [vR_zero]
        exact Submodule.zero_mem _
      smul_mem' := fun c {a} ha => by
        show vR τ hτ3 (c • a) ∈ spPt τ hτ3
        rw [vR_smul]
        exact Submodule.smul_mem _ c ha }
  have hX2 : Submodule.span K X2 ≤ Z := by
    rw [Submodule.span_le]
    rintro _ ⟨pq, rfl⟩
    exact vR_phi_mem τ hτ hτ3 h2 pq.1 pq.2
  have hX : ∀ z : F, z + τ (τ z) ∈ Submodule.span K X2 := by
    intro z
    have hz : z + τ (τ z) =
        (fun pq : F × F => pq.1 * τ (τ pq.2) + pq.2 * τ (τ pq.1)) (1, z) := by
      simp [add_comm]
    rw [hz]
    exact Submodule.subset_span ⟨(1, z), rfl⟩
  obtain ⟨b, hb⟩ := exists_tau_ne τ hτ hF hK
  obtain ⟨d, hd⟩ : ∃ d : F, d = τ (τ b) + τ b := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by
    rw [hd]
    intro h
    apply hb
    have h' : τ (τ b) = τ b := by linear_combination h - (τ b) * h2
    have h'' : b = τ (τ b) := by
      have := congrArg τ h'
      rw [hτ3] at this
      exact this
    exact (h''.trans h').symm
  have hvmem : d⁻¹ * τ (τ b) + b * τ (τ d⁻¹) ∈ X2 := ⟨(d⁻¹, b), rfl⟩
  have hvt : tr3 τ (d⁻¹ * τ (τ b) + b * τ (τ d⁻¹)) ≠ 0 := by
    rw [tr3_mul_add τ hτ3 d⁻¹ b, ← hd, inv_mul_cancel₀ hd0]
    have h1 : tr3 τ 1 = 1 := by
      simp only [tr3, map_one]
      linear_combination h2
    rw [h1]
    exact one_ne_zero
  have hZ : Submodule.span K X2 = ⊤ :=
    span_eq_top_of_tr τ hτ hτ3 hF hK h2 X2 hX hvmem hvt
  have hr : r ∈ Z := hX2 (hZ ▸ Submodule.mem_top)
  exact hr

theorem vP_mem_spPt [Fintype K] [Fintype F] (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ Fintype.card K)
    (hτ3 : ∀ a, τ (τ (τ a)) = a) (hF : Fintype.card F = Fintype.card K ^ 3)
    (hK : 4 ≤ Fintype.card K) (h2 : (2 : F) = 0) (p : F) : vP τ hτ3 p ∈ spPt τ hτ3 := by
  obtain ⟨k, h⟩ := pt_one_eq τ hτ hτ3 p
  have hmem : vP τ hτ3 p =
      vPt τ hτ3 ![1, τ p] - (vE0 τ + k • vE1 τ + vR τ hτ3 (p * τ (τ p))) := by
    rw [h]
    abel
  rw [hmem]
  refine Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.add_mem _ (Submodule.add_mem _ (vE0_mem τ hτ3)
      (Submodule.smul_mem _ _ (vE1_mem τ hτ3))) (vR_mem_spPt τ hτ hτ3 hF hK h2 _))

theorem mem_spPt_all [Fintype K] [Fintype F] (τ : F →ₐ[K] F) (hτ : ∀ a, τ a = a ^ Fintype.card K)
    (hτ3 : ∀ a, τ (τ (τ a)) = a) (hF : Fintype.card F = Fintype.card K ^ 3)
    (hK : 4 ≤ Fintype.card K) (h2 : (2 : F) = 0) (x : kForm τ) : x ∈ spPt τ hτ3 := by
  obtain ⟨c0, c1, hx⟩ := kForm_decomp τ hτ hτ3 x
  rw [hx]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (vE0_mem τ hτ3)) (Submodule.smul_mem _ _ (vE1_mem τ hτ3)))
    (vP_mem_spPt τ hτ hτ3 hF hK h2 _)) (vR_mem_spPt τ hτ hτ3 hF hK h2 _)

theorem polar_add_left (x x' y : Hyp F) : polar (x + x') y = polar x y + polar x' y := by
  simp only [polar, Pi.add_apply]
  ring

theorem polar_add_right (x y y' : Hyp F) : polar x (y + y') = polar x y + polar x y' := by
  simp only [polar, Pi.add_apply]
  ring

theorem polar_smul_left (a : F) (x y : Hyp F) : polar (a • x) y = a * polar x y := by
  simp only [polar, Pi.smul_apply, smul_eq_mul]
  ring

theorem polar_smul_right (a : F) (x y : Hyp F) : polar x (a • y) = a * polar x y := by
  simp only [polar, Pi.smul_apply, smul_eq_mul]
  ring

@[expose] def betaDefect (τ : F →ₐ[K] F) (β : LinearMap.BilinForm K (kForm τ)) (c : K)
    (x y : kForm τ) : F :=
  algebraMap K F (β x y) - algebraMap K F c * polar (x : Hyp F) (y : Hyp F)

theorem betaDefect_add_left (τ : F →ₐ[K] F) (β : LinearMap.BilinForm K (kForm τ)) (c : K)
    (x x' y : kForm τ) :
    betaDefect τ β c (x + x') y = betaDefect τ β c x y + betaDefect τ β c x' y := by
  unfold betaDefect
  simp only [map_add, LinearMap.add_apply, Submodule.coe_add, polar_add_left]
  ring

theorem betaDefect_add_right (τ : F →ₐ[K] F) (β : LinearMap.BilinForm K (kForm τ)) (c : K)
    (x y y' : kForm τ) :
    betaDefect τ β c x (y + y') = betaDefect τ β c x y + betaDefect τ β c x y' := by
  unfold betaDefect
  simp only [map_add, LinearMap.add_apply, Submodule.coe_add, polar_add_right]
  ring

theorem coe_smul_K (τ : F →ₐ[K] F) (a : K) (x : kForm τ) :
    ((a • x : kForm τ) : Hyp F) = algebraMap K F a • (x : Hyp F) := by
  funext i j k
  simp [Algebra.smul_def]

theorem betaDefect_smul_left (τ : F →ₐ[K] F) (β : LinearMap.BilinForm K (kForm τ)) (c : K)
    (a : K) (x y : kForm τ) :
    betaDefect τ β c (a • x) y = algebraMap K F a * betaDefect τ β c x y := by
  unfold betaDefect
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, coe_smul_K, polar_smul_left,
    map_mul]
  ring

theorem betaDefect_smul_right (τ : F →ₐ[K] F) (β : LinearMap.BilinForm K (kForm τ)) (c : K)
    (a : K) (x y : kForm τ) :
    betaDefect τ β c x (a • y) = algebraMap K F a * betaDefect τ β c x y := by
  unfold betaDefect
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, coe_smul_K, polar_smul_right,
    map_mul]
  ring

theorem betaDefect_eq_zero [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hτ3 : ∀ a, τ (τ (τ a)) = a)
    (hF : Fintype.card F = Fintype.card K ^ 3) (hK : 4 ≤ Fintype.card K) (h2 : (2 : F) = 0)
    (h2K : (2 : K) = 0) (Q : kForm τ → K) (β : LinearMap.BilinForm K (kForm τ))
    (hQs : ∀ (a : K) (x : kForm τ), Q (a • x) = a ^ 2 * Q x)
    (hQa : ∀ x y, Q (x + y) = Q x + Q y + β x y)
    (hQg : ∀ (g : SL(2, F)) (x y : kForm τ),
      (y : Hyp F) = act (τ : F →+* F) (g : Mat2 F) (x : Hyp F) → Q y = Q x)
    (x y : kForm τ) :
    betaDefect τ β (β (vPt τ hτ3 (Pi.single 0 1)) (vPt τ hτ3 (Pi.single 1 1))) x y = 0 := by
  set cK := β (vPt τ hτ3 (Pi.single 0 1)) (vPt τ hτ3 (Pi.single 1 1)) with hcK
  have hpp : ∀ v w : Fin 2 → F, betaDefect τ β cK (vPt τ hτ3 v) (vPt τ hτ3 w) = 0 := by
    intro v w
    unfold betaDefect
    rw [sub_eq_zero]
    exact beta_pt_eq τ hτ hτ3 h2 h2K Q β hQs hQa hQg v w
  have hleft : ∀ x ∈ spPt τ hτ3, ∀ y ∈ spPt τ hτ3, betaDefect τ β cK x y = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, rfl⟩ := hy
        exact hpp v w
      | zero => simp [betaDefect, polar]
      | add y y' _ _ h1 h2' =>
        rw [betaDefect_add_right, h1, h2', add_zero]
      | smul a y _ h =>
        rw [betaDefect_smul_right, h, mul_zero]
    | zero => intro y _; simp [betaDefect, polar]
    | add x x' _ _ h1 h2' =>
      intro y hy
      rw [betaDefect_add_left, h1 y hy, h2' y hy, add_zero]
    | smul a x _ h =>
      intro y hy
      rw [betaDefect_smul_left, h y hy, mul_zero]
  exact hleft x (mem_spPt_all τ hτ hτ3 hF hK h2 x) y (mem_spPt_all τ hτ hτ3 hF hK h2 y)

@[expose] def uMat (t : F) : SL(2, F) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem act_uMat_embR [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hτ3 : ∀ a, τ (τ (τ a)) = a) (t r : F) :
    ∃ k : K, act (τ : F →+* F) ((uMat t : SL(2, F)) : Mat2 F) (embR τ r) =
      k • e0 F + embP τ (τ t * r + t * τ r) + embR τ r := by
  obtain ⟨k, hk⟩ := fix_mem_range τ hτ
    (r * (τ t * τ (τ t)) + t * τ (τ t) * τ r + t * τ t * τ (τ r))
    (by simp only [map_add, map_mul, hτ3]; ring)
  have hk' : algebraMap K F k = r * (τ t * τ (τ t)) + t * τ (τ t) * τ r + t * τ t * τ (τ r) := hk
  refine ⟨k, ?_⟩
  funext i j k'
  fin_cases i <;> fin_cases j <;> fin_cases k' <;>
    simp [act, uMat, embP, embR, e0, Fin.sum_univ_two, Algebra.smul_def, hk', hτ3, map_add,
      map_mul] <;>
    ring

theorem act_uMat_e1 [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hτ3 : ∀ a, τ (τ (τ a)) = a) (t : F) :
    ∃ k : K, algebraMap K F k = t * τ t * τ (τ t) ∧
      act (τ : F →+* F) ((uMat t : SL(2, F)) : Mat2 F) (e1 F) =
        k • e0 F + e1 F + embP τ (t * τ t) + embR τ t := by
  obtain ⟨k, hk⟩ := fix_mem_range τ hτ (t * τ t * τ (τ t))
    (by simp only [map_mul, hτ3]; ring)
  have hk' : algebraMap K F k = t * τ t * τ (τ t) := hk
  refine ⟨k, hk', ?_⟩
  funext i j k'
  fin_cases i <;> fin_cases j <;> fin_cases k' <;>
    simp [act, uMat, embP, embR, e0, e1, Fin.sum_univ_two, Algebra.smul_def, hk', hτ3, map_mul,
      map_add] <;>
    ring

theorem quad_embR (τ : F →ₐ[K] F) (r : F) : quad (embR τ r) = 0 := by
  simp [quad, embR]

theorem quad_I1 (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (h2 : (2 : F) = 0) (k : K)
    (t r : F) :
    quad (k • e0 F + embP τ (τ t * r + t * τ r) + embR τ r) = 0 := by
  simp [quad, e0, embP, embR, Algebra.smul_def, hτ3, map_add, map_mul]
  linear_combination (τ t * r * τ (τ r) + t * τ r * τ (τ r) + τ (τ t) * r * τ r) * h2

theorem quad_I2 (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (h2 : (2 : F) = 0) (k : K)
    (t : F) (hk : algebraMap K F k = t * τ t * τ (τ t)) :
    quad (k • e0 F + e1 F + embP τ (t * τ t) + embR τ t) = 0 := by
  have hk' := hk
  simp [quad, e0, e1, embP, embR, Algebra.smul_def, hτ3, map_add, map_mul, hk']
  linear_combination (2 * (t * τ t * τ (τ t))) * h2

theorem quad_smulF (a : F) (x : Hyp F) : quad (a • x) = a ^ 2 * quad x := by
  simp only [quad, Pi.smul_apply, smul_eq_mul]
  ring

theorem vP_add (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (p p' : F) :
    vP τ hτ3 (p + p') = vP τ hτ3 p + vP τ hτ3 p' :=
  Subtype.ext (embP_add τ p p')

theorem vP_smul (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (c : K) (p : F) :
    vP τ hτ3 (c • p) = c • vP τ hτ3 p :=
  Subtype.ext (embP_smul τ c p)

theorem vP_zero (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) : vP τ hτ3 0 = 0 := by
  apply Subtype.ext
  funext i j k
  simp [vP, embP]

theorem tr3_expand (τ : F →ₐ[K] F) (hτ3 : ∀ a, τ (τ (τ a)) = a) (s r : F) :
    tr3 τ (s * r + τ (τ s) * τ r) = tr3 τ (s * (r + τ (τ r))) := by
  simp only [tr3, map_add, map_mul, hτ3]
  ring

theorem tr3_one (τ : F →ₐ[K] F) (h2 : (2 : F) = 0) : tr3 τ 1 = 1 := by
  simp only [tr3, map_one]
  linear_combination h2

@[expose] def fDef (τ : F →ₐ[K] F) (Q : kForm τ → K) (c : K) (x : kForm τ) : F :=
  algebraMap K F (Q x) - algebraMap K F c * quad (x : Hyp F)

theorem fDef_add (τ : F →ₐ[K] F) (Q : kForm τ → K) (β : LinearMap.BilinForm K (kForm τ))
    (c : K) (hQa : ∀ x y, Q (x + y) = Q x + Q y + β x y)
    (hβ : ∀ x y : kForm τ,
      algebraMap K F (β x y) = algebraMap K F c * polar (x : Hyp F) (y : Hyp F))
    (x y : kForm τ) : fDef τ Q c (x + y) = fDef τ Q c x + fDef τ Q c y := by
  unfold fDef
  rw [hQa]
  simp only [map_add, Submodule.coe_add, quad_add, hβ]
  ring

theorem fDef_smul (τ : F →ₐ[K] F) (Q : kForm τ → K) (c : K)
    (hQs : ∀ (a : K) (x : kForm τ), Q (a • x) = a ^ 2 * Q x) (a : K) (x : kForm τ) :
    fDef τ Q c (a • x) = algebraMap K F (a ^ 2) * fDef τ Q c x := by
  unfold fDef
  rw [hQs]
  simp only [map_mul, map_pow, coe_smul_K, quad_smulF]
  ring

theorem fDef_zero (τ : F →ₐ[K] F) (Q : kForm τ → K) (c : K)
    (hQs : ∀ (a : K) (x : kForm τ), Q (a • x) = a ^ 2 * Q x) : fDef τ Q c 0 = 0 := by
  have hQ0 : Q 0 = 0 := by simpa using hQs 0 0
  unfold fDef
  rw [hQ0]
  simp [quad]

theorem invariant_quad_eq_quad [Fintype K] [Fintype F] (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) (hF : Fintype.card F = Fintype.card K ^ 3)
    (hK : 4 ≤ Fintype.card K) (h2K : (2 : K) = 0)
    (Q : kForm τ → K) (β : LinearMap.BilinForm K (kForm τ))
    (hQs : ∀ (a : K) (x : kForm τ), Q (a • x) = a ^ 2 * Q x)
    (hQa : ∀ x y, Q (x + y) = Q x + Q y + β x y)
    (hQg : ∀ (g : SL(2, F)) (x y : kForm τ),
      (y : Hyp F) = act (τ : F →+* F) (g : Mat2 F) (x : Hyp F) → Q y = Q x) :
    ∃ c : K, ∀ x : kForm τ, algebraMap K F (Q x) = algebraMap K F c * quad (x : Hyp F) := by
  have hτ3 : ∀ a, τ (τ (τ a)) = a := tau_cube τ hτ hF
  have h2 : (2 : F) = 0 := by
    have h := congrArg (algebraMap K F) h2K
    rw [map_ofNat, map_zero] at h
    exact h
  obtain ⟨cK, hcK⟩ : ∃ cK : K,
      cK = β (vPt τ hτ3 (Pi.single 0 1)) (vPt τ hτ3 (Pi.single 1 1)) := ⟨_, rfl⟩
  have hβ : ∀ x y : kForm τ,
      algebraMap K F (β x y) = algebraMap K F cK * polar (x : Hyp F) (y : Hyp F) := by
    intro x y
    rw [hcK]
    exact sub_eq_zero.mp (betaDefect_eq_zero τ hτ hτ3 hF hK h2 h2K Q β hQs hQa hQg x y)
  have hQE0 : Q (vE0 τ) = 0 := by
    rw [vE0_eq τ hτ3]
    exact Q_vPt_eq_zero τ hτ hτ3 hF hK h2K Q hQs hQg _
  have hQE1 : Q (vE1 τ) = 0 := by
    rw [vE1_eq τ hτ3]
    exact Q_vPt_eq_zero τ hτ hτ3 hF hK h2K Q hQs hQg _
  have hfadd := fDef_add τ Q β cK hQa hβ
  have hfsmul := fDef_smul τ Q cK hQs
  have hfE0 : fDef τ Q cK (vE0 τ) = 0 := by
    unfold fDef
    rw [hQE0, show ((vE0 τ : kForm τ) : Hyp F) = e0 F from rfl, quad_e0]
    simp
  have hfE1 : fDef τ Q cK (vE1 τ) = 0 := by
    unfold fDef
    rw [hQE1, show ((vE1 τ : kForm τ) : Hyp F) = e1 F from rfl, quad_e1]
    simp
  have U1 : ∀ t r : F, fDef τ Q cK (vP τ hτ3 (τ t * r + t * τ r)) = 0 := by
    intro t r
    obtain ⟨k, hk⟩ := act_uMat_embR τ hτ hτ3 t r
    have hcoe : ((k • vE0 τ + vP τ hτ3 (τ t * r + t * τ r) + vR τ hτ3 r : kForm τ) : Hyp F) =
        k • e0 F + embP τ (τ t * r + t * τ r) + embR τ r := by
      simp [vE0, vP, vR]
    have hvR : ((vR τ hτ3 r : kForm τ) : Hyp F) = embR τ r := rfl
    have hy1 : ((k • vE0 τ + vP τ hτ3 (τ t * r + t * τ r) + vR τ hτ3 r : kForm τ) : Hyp F) =
        act (τ : F →+* F) ((uMat t : SL(2, F)) : Mat2 F) ((vR τ hτ3 r : kForm τ) : Hyp F) := by
      rw [hcoe, hvR, hk]
    have hQ1 := hQg (uMat t) (vR τ hτ3 r) _ hy1
    have hquad1 : quad ((k • vE0 τ + vP τ hτ3 (τ t * r + t * τ r) + vR τ hτ3 r : kForm τ) :
        Hyp F) = 0 := by
      rw [hcoe]
      exact quad_I1 τ hτ3 h2 k t r
    have hquad2 : quad ((vR τ hτ3 r : kForm τ) : Hyp F) = 0 := by
      rw [hvR]
      exact quad_embR τ r
    have hf1 : fDef τ Q cK (k • vE0 τ + vP τ hτ3 (τ t * r + t * τ r) + vR τ hτ3 r) =
        fDef τ Q cK (vR τ hτ3 r) := by
      unfold fDef
      rw [hQ1, hquad1, hquad2]
    have hsplit : fDef τ Q cK (k • vE0 τ + vP τ hτ3 (τ t * r + t * τ r) + vR τ hτ3 r) =
        fDef τ Q cK (k • vE0 τ) + fDef τ Q cK (vP τ hτ3 (τ t * r + t * τ r)) +
          fDef τ Q cK (vR τ hτ3 r) := by
      rw [hfadd, hfadd]
    have hk0 : fDef τ Q cK (k • vE0 τ) = 0 := by
      rw [hfsmul, hfE0, mul_zero]
    linear_combination (-1 : F) * hsplit + hf1 - hk0
  have U2 : ∀ t : F, fDef τ Q cK (vP τ hτ3 (t * τ t)) + fDef τ Q cK (vR τ hτ3 t) = 0 := by
    intro t
    obtain ⟨k, hkval, hk⟩ := act_uMat_e1 τ hτ hτ3 t
    have hcoe : ((k • vE0 τ + vE1 τ + vP τ hτ3 (t * τ t) + vR τ hτ3 t : kForm τ) : Hyp F) =
        k • e0 F + e1 F + embP τ (t * τ t) + embR τ t := by
      simp [vE0, vE1, vP, vR]
    have hvE1 : ((vE1 τ : kForm τ) : Hyp F) = e1 F := rfl
    have hy2 : ((k • vE0 τ + vE1 τ + vP τ hτ3 (t * τ t) + vR τ hτ3 t : kForm τ) : Hyp F) =
        act (τ : F →+* F) ((uMat t : SL(2, F)) : Mat2 F) ((vE1 τ : kForm τ) : Hyp F) := by
      rw [hcoe, hvE1, hk]
    have hQ2 := hQg (uMat t) (vE1 τ) _ hy2
    have hquad2 : quad ((k • vE0 τ + vE1 τ + vP τ hτ3 (t * τ t) + vR τ hτ3 t : kForm τ) :
        Hyp F) = 0 := by
      rw [hcoe]
      exact quad_I2 τ hτ3 h2 k t hkval
    have hquadE1 : quad ((vE1 τ : kForm τ) : Hyp F) = 0 := by
      rw [hvE1]
      exact quad_e1
    have hf2 : fDef τ Q cK (k • vE0 τ + vE1 τ + vP τ hτ3 (t * τ t) + vR τ hτ3 t) =
        fDef τ Q cK (vE1 τ) := by
      unfold fDef
      rw [hQ2, hquad2, hquadE1]
    have hsplit : fDef τ Q cK (k • vE0 τ + vE1 τ + vP τ hτ3 (t * τ t) + vR τ hτ3 t) =
        fDef τ Q cK (k • vE0 τ) + fDef τ Q cK (vE1 τ) + fDef τ Q cK (vP τ hτ3 (t * τ t)) +
          fDef τ Q cK (vR τ hτ3 t) := by
      rw [hfadd, hfadd, hfadd]
    have hk0 : fDef τ Q cK (k • vE0 τ) = 0 := by
      rw [hfsmul, hfE0, mul_zero]
    linear_combination (-1 : F) * hsplit + hf2 - hk0
  obtain ⟨b, hb⟩ := exists_tau_ne τ hτ hF hK
  obtain ⟨c0, hc0⟩ : ∃ c0 : F, c0 = b + τ (τ b) := ⟨_, rfl⟩
  have hc0ne : c0 ≠ 0 := by
    rw [hc0]
    intro h
    apply hb
    have h1 : τ (τ b) = b := by linear_combination h - b * h2
    have h3 := congrArg τ h1
    rw [hτ3] at h3
    exact h3.symm
  obtain ⟨s, hs⟩ : ∃ s : F, s = c0⁻¹ := ⟨_, rfl⟩
  have hsc : s * c0 = 1 := by
    rw [hs]
    exact inv_mul_cancel₀ hc0ne
  set X1 : Set F := Set.range (fun tr : F × F => τ tr.1 * tr.2 + tr.1 * τ tr.2) with hX1def
  have hX1 : ∀ z : F, z + τ (τ z) ∈ Submodule.span K X1 := by
    intro z
    have e : z + τ (τ z) = (fun tr : F × F => τ tr.1 * tr.2 + tr.1 * τ tr.2) (1, τ (τ z)) := by
      simp [hτ3, add_comm]
    rw [e]
    exact Submodule.subset_span ⟨(1, τ (τ z)), rfl⟩
  have hvmem : s * b + τ (τ s) * τ b ∈ X1 := by
    have hv_eq : τ (τ (τ s)) * b + τ (τ s) * τ b = s * b + τ (τ s) * τ b := by
      rw [hτ3]
    rw [← hv_eq]
    exact ⟨(τ (τ s), b), rfl⟩
  have hvt : tr3 τ (s * b + τ (τ s) * τ b) ≠ 0 := by
    rw [tr3_expand τ hτ3, ← hc0, hsc, tr3_one τ h2]
    exact one_ne_zero
  have hspanX1 : Submodule.span K X1 = ⊤ :=
    span_eq_top_of_tr τ hτ hτ3 hF hK h2 X1 hX1 hvmem hvt
  let ZL : Submodule K F :=
    { carrier := {p | fDef τ Q cK (vP τ hτ3 p) = 0}
      add_mem' := fun {a a'} ha ha' => by
        have ha0 : fDef τ Q cK (vP τ hτ3 a) = 0 := ha
        have ha0' : fDef τ Q cK (vP τ hτ3 a') = 0 := ha'
        show fDef τ Q cK (vP τ hτ3 (a + a')) = 0
        rw [vP_add, hfadd, ha0, ha0', add_zero]
      zero_mem' := by
        show fDef τ Q cK (vP τ hτ3 0) = 0
        rw [vP_zero, fDef_zero τ Q cK hQs]
      smul_mem' := fun c {a} ha => by
        have ha0 : fDef τ Q cK (vP τ hτ3 a) = 0 := ha
        show fDef τ Q cK (vP τ hτ3 (c • a)) = 0
        rw [vP_smul, hfsmul, ha0, mul_zero] }
  have hX1sub : X1 ⊆ (ZL : Set F) := by
    rintro _ ⟨⟨t, r⟩, rfl⟩
    exact U1 t r
  have hZtop : (⊤ : Submodule K F) ≤ ZL := by
    rw [← hspanX1]
    exact Submodule.span_le.mpr hX1sub
  have U3 : ∀ p : F, fDef τ Q cK (vP τ hτ3 p) = 0 := fun p =>
    hZtop (Submodule.mem_top (x := p))
  have U4 : ∀ t : F, fDef τ Q cK (vR τ hτ3 t) = 0 := by
    intro t
    have h := U2 t
    rw [U3 (t * τ t), zero_add] at h
    exact h
  refine ⟨cK, fun x => ?_⟩
  obtain ⟨c0', c1', hx⟩ := kForm_decomp τ hτ hτ3 x
  have hfx : fDef τ Q cK x = 0 := by
    rw [hx, hfadd, hfadd, hfadd, hfsmul, hfsmul, hfE0, hfE1, U3, U4]
    simp
  unfold fDef at hfx
  exact sub_eq_zero.mp hfx

theorem invariant_quad_eq_quad_frob [Fintype K] [Fintype F]
    (hF : Fintype.card F = Fintype.card K ^ 3) (hK : 4 ≤ Fintype.card K) (h2K : (2 : K) = 0)
    (Q : kForm (FiniteField.frobeniusAlgHom K F) → K)
    (β : LinearMap.BilinForm K (kForm (FiniteField.frobeniusAlgHom K F)))
    (hQs : ∀ (a : K) (x : kForm (FiniteField.frobeniusAlgHom K F)), Q (a • x) = a ^ 2 * Q x)
    (hQa : ∀ x y, Q (x + y) = Q x + Q y + β x y)
    (hQg : ∀ (g : SL(2, F)) (x y : kForm (FiniteField.frobeniusAlgHom K F)),
      (y : Hyp F) = act ((FiniteField.frobeniusAlgHom K F : F →ₐ[K] F) : F →+* F)
        (g : Mat2 F) (x : Hyp F) → Q y = Q x) :
    ∃ c : K, ∀ x : kForm (FiniteField.frobeniusAlgHom K F),
      algebraMap K F (Q x) = algebraMap K F c * quad (x : Hyp F) :=
  invariant_quad_eq_quad (FiniteField.frobeniusAlgHom K F) (fun _ => rfl) hF hK h2K Q β hQs hQa
    hQg

end Basic

end CFSG.RankThree.GF2n.Smith81.D3

end
