module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddBase
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryField

public section

namespace CFSG.StandardType

namespace OrthBstarOdd

open Module QuadraticMap

section Field

variable {K : Type} [Field K] {τ : K}

@[expose] def liftAut (σ : K ≃+* K) (hστ : σ τ = τ) :
    QuadraticAlgebra K 1 τ ≃+* QuadraticAlgebra K 1 τ where
  toFun z := ⟨σ z.re, σ z.im⟩
  invFun z := ⟨σ.symm z.re, σ.symm z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by
    ext
    · simp only [QuadraticAlgebra.re_mul, map_add, map_mul, map_one]
    · simp only [QuadraticAlgebra.im_mul, map_add, map_mul, hστ]
  map_add' z w := by ext <;> simp

theorem liftAut_re (σ : K ≃+* K) (hστ : σ τ = τ) (z : QuadraticAlgebra K 1 τ) :
    (liftAut σ hστ z).re = σ z.re := rfl

theorem liftAut_im (σ : K ≃+* K) (hστ : σ τ = τ) (z : QuadraticAlgebra K 1 τ) :
    (liftAut σ hστ z).im = σ z.im := rfl

theorem liftAut_star (σ : K ≃+* K) (hστ : σ τ = τ) (z : QuadraticAlgebra K 1 τ) :
    liftAut σ hστ (star z) = star (liftAut σ hστ z) := by
  ext <;> simp [liftAut_re, liftAut_im, hστ]

theorem liftAut_pow (σ : K ≃+* K) (hστ : σ τ = τ) (k : ℕ) (z : QuadraticAlgebra K 1 τ) :
    (liftAut σ hστ ^ k) z = ⟨(σ ^ k) z.re, (σ ^ k) z.im⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', RingAut.mul_apply, ih, pow_succ', RingAut.mul_apply, RingAut.mul_apply]
    rfl

theorem liftAut_pow_eq_one {σ : K ≃+* K} (hστ : σ τ = τ) {p : ℕ} (hσp : σ ^ p = 1) :
    liftAut σ hστ ^ p = 1 := by
  refine RingEquiv.ext fun z => ?_
  rw [liftAut_pow, hσp]
  rfl

theorem liftAut_ne_one {σ : K ≃+* K} (hστ : σ τ = τ) (hσ1 : σ ≠ 1) : liftAut σ hστ ≠ 1 := by
  intro h
  apply hσ1
  refine RingEquiv.ext fun x => ?_
  have := congrArg QuadraticAlgebra.re (RingEquiv.congr_fun h ⟨x, 0⟩)
  exact this

variable [Finite K] [CharP K 2] [Fact (∀ r : K, r ^ 2 ≠ 1 + τ * r)]

theorem exists_norm_one_eq_mul {p : ℕ} (hp : p.Prime)
    {φ : QuadraticAlgebra K 1 τ ≃+* QuadraticAlgebra K 1 τ} (hφp : φ ^ p = 1) (hφ1 : φ ≠ 1)
    (hφs : ∀ z, φ (star z) = star (φ z)) {γ : QuadraticAlgebra K 1 τ}
    (hγN : QuadraticAlgebra.norm γ = 1) (hγp : TableBUF.partNorm φ γ p = 1) :
    ∃ c : QuadraticAlgebra K 1 τ, QuadraticAlgebra.norm c = 1 ∧ φ c = γ * c := by
  classical
  have : Finite (QuadraticAlgebra K 1 τ) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd (1 : K) τ).symm
  have : Fintype (QuadraticAlgebra K 1 τ) := Fintype.ofFinite _
  have : CharP (QuadraticAlgebra K 1 τ) 2 :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective 2
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have h2L : (2 : QuadraticAlgebra K 1 τ) = 0 := CharTwo.two_eq_zero
  obtain ⟨δ, hδ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq (QuadraticAlgebra K 1 τ) 2) γ
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hδ
    rw [hδ, QuadraticAlgebra.norm_zero] at hγN
    exact zero_ne_one hγN
  have hNδ : QuadraticAlgebra.norm δ = 1 := by
    have h1 : QuadraticAlgebra.norm δ * QuadraticAlgebra.norm δ = 1 := by
      rw [← map_mul, ← hδ, hγN]
    have h2 : (QuadraticAlgebra.norm δ - 1) ^ 2 = 0 := by
      linear_combination h1 + (1 - QuadraticAlgebra.norm δ) * h2K
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  have hPδ : TableBUF.partNorm φ δ p = 1 := by
    have h1 : TableBUF.partNorm φ δ p ^ 2 = 1 := by
      rw [← TableBUF.partNorm_pow, _root_.sq, ← hδ, hγp]
    have h2 : (TableBUF.partNorm φ δ p - 1) ^ 2 = 0 := by
      linear_combination h1 + (1 - TableBUF.partNorm φ δ p) * h2L
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  obtain ⟨b, hb0, hb⟩ := TableBUF.exists_hilbert90 hp hφp hφ1 hδ0 hPδ
  have hsδ : star δ = δ⁻¹ := by
    have h := QuadraticAlgebra.algebraMap_norm_eq_mul_star δ
    rw [hNδ, map_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hNb : QuadraticAlgebra.norm b ≠ 0 := fun h =>
    hb0 (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h)
  refine ⟨star b * b⁻¹, ?_, ?_⟩
  · have h1 : QuadraticAlgebra.norm b⁻¹ * QuadraticAlgebra.norm b = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hb0, map_one]
    rw [map_mul, QuadraticAlgebra.norm_star, mul_comm]
    exact h1
  · have hsb0 : star b ≠ 0 := by
      intro h
      apply hb0
      have := congrArg star h
      rwa [star_star, star_zero] at this
    rw [map_mul, hφs, map_inv₀, hb, star_mul', star_inv₀, hsδ, inv_inv, hδ]
    field_simp

end Field

section Action

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {τ : K}

@[expose] def lact (s : V ≃ₗ[K] V) (z : QuadraticAlgebra K 1 τ) (v : V) : V :=
  z.re • v + z.im • s v

theorem lact_def (s : V ≃ₗ[K] V) (z : QuadraticAlgebra K 1 τ) (v : V) :
    lact s z v = z.re • v + z.im • s v := rfl

theorem lact_sub_left (s : V ≃ₗ[K] V) (z z' : QuadraticAlgebra K 1 τ) (v : V) :
    lact s (z - z') v = lact s z v - lact s z' v := by
  simp only [lact_def, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, sub_smul]
  abel

theorem lact_add_right (s : V ≃ₗ[K] V) (z : QuadraticAlgebra K 1 τ) (v v' : V) :
    lact s z (v + v') = lact s z v + lact s z v' := by
  simp only [lact_def, map_add, smul_add]
  abel

theorem lact_algebraMap (s : V ≃ₗ[K] V) (c : K) (v : V) :
    lact s (algebraMap K (QuadraticAlgebra K 1 τ) c) v = c • v := by
  simp [lact_def, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]

theorem lact_one (s : V ≃ₗ[K] V) (v : V) : lact s (1 : QuadraticAlgebra K 1 τ) v = v := by
  rw [lact_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, one_smul, zero_smul, add_zero]

theorem lact_zero_left (s : V ≃ₗ[K] V) (v : V) : lact s (0 : QuadraticAlgebra K 1 τ) v = 0 := by
  simp [lact_def]

theorem lact_mem (s : V ≃ₗ[K] V) {S : Submodule K V} (hsS : ∀ v ∈ S, s v ∈ S)
    (z : QuadraticAlgebra K 1 τ) {v : V} (hv : v ∈ S) : lact s z v ∈ S :=
  S.add_mem (S.smul_mem _ hv) (S.smul_mem _ (hsS v hv))

theorem lact_mul (s : V ≃ₗ[K] V) (z z' : QuadraticAlgebra K 1 τ) {v : V}
    (hv : s (s v) = τ • s v + v) : lact s (z * z') v = lact s z (lact s z' v) := by
  simp only [lact_def, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_smul, hv]
  module

theorem map_lact [CharP K 2] {Q : QuadraticForm K V} {s : V ≃ₗ[K] V} (hsQ : ∀ v, Q (s v) = Q v)
    (hτ : τ ≠ 0) (z : QuadraticAlgebra K 1 τ) {v : V} (hv : s (s v) = τ • s v + v) :
    Q (lact s z v) = QuadraticAlgebra.norm z * Q v := by
  rw [lact_def, map_add_smul_of_sq hsQ hτ hv, QuadraticAlgebra.norm_def]
  linear_combination (z.im * z.im * Q v) * CharTwo.two_eq_zero (R := K)

theorem semi_lact {G : V ≃+ V} {σ : K ≃+* K} (hGs : ∀ (c : K) v, G (c • v) = σ c • G v)
    {s : V ≃ₗ[K] V} (hGc : ∀ v, G (s v) = s (G v)) (hστ : σ τ = τ) (z : QuadraticAlgebra K 1 τ)
    (v : V) : G (lact s z v) = lact s (liftAut σ hστ z) (G v) := by
  rw [lact_def, lact_def, map_add, hGs, hGs, hGc, liftAut_re, liftAut_im]

end Action

section Line

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem irred_of_fpf {p : ℕ} (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {s : V ≃ₗ[K] V} (hsp : s ^ p = 1)
    {τ : K} {W : Submodule K V} (hW : W ≠ ⊥) (hsW : ∀ v ∈ W, s v ∈ W)
    (hfpf : ∀ v ∈ W, v ≠ 0 → s v ≠ v) (hsq : ∀ v ∈ W, s (s v) = τ • s v + v) :
    ∀ r : K, r ^ 2 ≠ 1 + τ * r := by
  intro r hr
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  set u := s w - r • w with hu
  have huW : u ∈ W := W.sub_mem (hsW w hwW) (W.smul_mem r hwW)
  have hsu : s u = (τ - r) • u := by
    have hc : (τ - r) * r = -1 := by linear_combination (-1 : K) * hr
    have e1 : s u = τ • s w + w - r • s w := by
      rw [hu, map_sub, map_smul, hsq w hwW]
    have e2 : (τ - r) • u = (τ - r) • s w - ((τ - r) * r) • w := by
      rw [hu, smul_sub, smul_smul]
    rw [e1, e2, hc]
    module
  by_cases hu0 : u = 0
  · exact hfpf w hwW hw0 (apply_eq_of_eigen hsp hK1 hw0 (sub_eq_zero.mp hu0))
  · exact hfpf u huW hu0 (apply_eq_of_eigen hsp hK1 hu0 hsu)

theorem exists_isotropic_line {p : ℕ} (hp : p.Prime) (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    {Q : QuadraticForm K V} {E : Subgroup (V ≃ₗ[K] V)} {W W' : Submodule K V} {s : V ≃ₗ[K] V}
    {τ : K} (hFD : FrameData Q E W W' s τ) (hsQ : ∀ v, Q (s v) = Q v) (hsp : s ^ p = 1)
    (hsW : ∀ v ∈ W, s v ∈ W) (hsW' : ∀ v ∈ W', s v ∈ W') {G : V ≃+ V} {σ : K ≃+* K}
    (hGs : ∀ (c : K) v, G (c • v) = σ c • G v) {μ : K} (hGQ : ∀ v, Q (G v) = μ * σ (Q v))
    (hGW : ∀ v ∈ W, G v ∈ W) (hGW' : ∀ v ∈ W', G v ∈ W') (hGc : ∀ v, G (s v) = s (G v))
    {a : K} (hGp : ∀ v, (⇑G)^[p] v = a • v) (hσp : σ ^ p = 1) (hσ1 : σ ≠ 1) :
    ∃ x ∈ W ⊔ W', (∀ c d : K, Q (c • x + d • s x) = 0) ∧
      (∀ c d : K, c • x + d • s x = 0 → c = 0 ∧ d = 0) ∧ ∃ α β : K, G x = α • x + β • s x := by
  classical
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ := hFD.tau_ne
  have hsq := hFD.sq
  have hWsup : ∀ v ∈ W, v ∈ W ⊔ W' := fun v hv => Submodule.mem_sup_left hv
  have hW'sup : ∀ v ∈ W', v ∈ W ⊔ W' := fun v hv => Submodule.mem_sup_right hv
  have hne : ∀ {S : Submodule K V}, finrank K S = 2 → S ≠ ⊥ := fun hS h => by
    rw [h, finrank_bot] at hS
    exact absurd hS (by norm_num)
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne hFD.finrank_left)
  obtain ⟨w₀, hw₀W, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne hFD.finrank_right)
  have hQw := hFD.aniso_left w hwW hw0
  have hQw₀ := hFD.aniso_right w₀ hw₀W hw₀0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q w / Q w₀)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hr
    exact hr.elim hQw hQw₀
  set w' := r • w₀ with hw'def
  have hw'W : w' ∈ W' := W'.smul_mem r hw₀W
  have hw'0 : w' ≠ 0 := smul_ne_zero hr0 hw₀0
  have hQw' : Q w' = Q w := by
    rw [hw'def, QuadraticMap.map_smul, smul_eq_mul, ← hr, div_mul_cancel₀ _ hQw₀]
  have hGinj : ∀ v, G v = 0 → v = 0 := fun v h => G.injective (h.trans (map_zero G).symm)
  have hστ : σ τ = τ := by
    have hGw0 : G w ≠ 0 := fun h => hw0 (hGinj w h)
    have e1 : G (s (s w)) = s (s (G w)) := by rw [hGc, hGc]
    rw [hsq w (hWsup w hwW), map_add, hGs, hGc, hsq (G w) (hWsup _ (hGW w hwW))] at e1
    have e2 : (σ τ - τ) • s (G w) = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr (add_right_cancel e1)
    have hsGw : s (G w) ≠ 0 := fun h => hGw0 (s.injective (h.trans (map_zero s).symm))
    exact sub_eq_zero.mp ((smul_eq_zero.mp e2).resolve_right hsGw)
  have : Fact (∀ r : K, r ^ 2 ≠ 1 + τ * r) :=
    ⟨irred_of_fpf hK1 hsp (hne hFD.finrank_left) hsW hFD.fpf_left
      (fun v hv => hsq v (hWsup v hv))⟩
  set φ := liftAut σ hστ with hφ
  have hindW := indep_of_ne hsp hK1 (hFD.fpf_left w hwW hw0)
  have hindW' := indep_of_ne hsp hK1 (hFD.fpf_right w' hw'W hw'0)
  have hfree : ∀ {v : V}, (∀ c d : K, c • v + d • s v = 0 → c = 0 ∧ d = 0) →
      ∀ z : QuadraticAlgebra K 1 τ, lact s z v = 0 → z = 0 := by
    intro v hv z hz
    obtain ⟨h1, h2⟩ := hv z.re z.im hz
    ext
    · exact h1
    · exact h2
  obtain ⟨c₁, d₁, hl₁e⟩ := mem_span_of_finrank_two hFD.finrank_left hwW (hsW w hwW) hindW (G w)
    (hGW w hwW)
  obtain ⟨c₂, d₂, hl₂e⟩ := mem_span_of_finrank_two hFD.finrank_right hw'W (hsW' w' hw'W) hindW'
    (G w') (hGW' w' hw'W)
  set l₁ : QuadraticAlgebra K 1 τ := ⟨c₁, d₁⟩ with hl₁
  set l₂ : QuadraticAlgebra K 1 τ := ⟨c₂, d₂⟩ with hl₂
  have hGw : G w = lact s l₁ w := hl₁e
  have hGw' : G w' = lact s l₂ w' := hl₂e
  have hiter : ∀ {v : V} {l : QuadraticAlgebra K 1 τ}, v ∈ W ⊔ W' → G v = lact s l v →
      ∀ k : ℕ, (⇑G)^[k] v = lact s (TableBUF.partNorm φ l k) v := by
    intro v l hv hGv k
    induction k with
    | zero =>
      rw [Function.iterate_zero_apply, TableBUF.partNorm, Finset.prod_range_zero, lact_one]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, semi_lact hGs hGc hστ, hGv,
        ← lact_mul s _ _ (hsq v hv), TableBUF.partNorm_succ', mul_comm]
  have hPa : ∀ {v : V} {l : QuadraticAlgebra K 1 τ}, v ∈ W ⊔ W' → G v = lact s l v →
      (∀ c d : K, c • v + d • s v = 0 → c = 0 ∧ d = 0) →
      TableBUF.partNorm φ l p = algebraMap K (QuadraticAlgebra K 1 τ) a := by
    intro v l hv hGv hindv
    have h1 := hiter hv hGv p
    rw [hGp v, ← lact_algebraMap (τ := τ) s a v] at h1
    have h2 : lact s (TableBUF.partNorm φ l p - algebraMap K _ a) v = 0 := by
      rw [lact_sub_left, h1, sub_self]
    exact sub_eq_zero.mp (hfree hindv _ h2)
  have hP₁ := hPa (hWsup w hwW) hGw hindW
  have hP₂ := hPa (hW'sup w' hw'W) hGw' hindW'
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 := hGp w
    rw [zero_smul] at h1
    have h2 : (⇑G)^[p] 0 = 0 := Function.iterate_fixed (map_zero G) p
    exact hw0 ((Function.Injective.iterate G.injective p) (h1.trans h2.symm))
  have hl₂0 : l₂ ≠ 0 := by
    rintro h
    rw [h, lact_zero_left] at hGw'
    exact hw'0 (hGinj w' hGw')
  set γ := l₁ * l₂⁻¹ with hγ
  have hγp : TableBUF.partNorm φ γ p = 1 := by
    have e : TableBUF.partNorm φ γ p = TableBUF.partNorm φ l₁ p * (TableBUF.partNorm φ l₂ p)⁻¹ := by
      simp only [hγ, TableBUF.partNorm, map_mul, map_inv₀, Finset.prod_mul_distrib,
        Finset.prod_inv_distrib]
    rw [e, hP₁, hP₂, mul_inv_cancel₀]
    exact (map_ne_zero _).mpr ha0
  have hN : QuadraticAlgebra.norm l₁ = QuadraticAlgebra.norm l₂ := by
    have e1 := hGQ w
    have e2 := hGQ w'
    rw [hGw, map_lact hsQ hτ l₁ (hsq w (hWsup w hwW))] at e1
    rw [hGw', map_lact hsQ hτ l₂ (hsq w' (hW'sup w' hw'W)), hQw'] at e2
    exact mul_right_cancel₀ hQw (e1.trans e2.symm)
  have hγN : QuadraticAlgebra.norm γ = 1 := by
    have h1 : QuadraticAlgebra.norm l₂ * QuadraticAlgebra.norm l₂⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hl₂0, map_one]
    rw [hγ, map_mul, hN, h1]
  obtain ⟨c, hcN, hc⟩ := exists_norm_one_eq_mul hp (liftAut_pow_eq_one hστ hσp)
    (liftAut_ne_one hστ hσ1) (liftAut_star σ hστ) hγN hγp
  have hcw'W : lact s c w' ∈ W' := lact_mem s hsW' c hw'W
  have hdisj : ∀ v, v ∈ W → v ∈ W' → v = 0 := by
    intro v hv hv'
    by_contra hv0
    have h1 := polar_eq_of_sq hsQ hτ (hsq v (hWsup v hv))
    rw [QuadraticMap.polar_comm, hFD.orth (s v) (hsW v hv) v hv'] at h1
    exact hFD.aniso_left v hv hv0 ((mul_eq_zero.mp h1.symm).resolve_left hτ)
  refine ⟨w + lact s c w', Submodule.add_mem_sup hwW hcw'W, ?_, ?_, l₁.re, l₁.im, ?_⟩
  · intro c' d'
    set z : QuadraticAlgebra K 1 τ := ⟨c', d'⟩ with hz
    have e : c' • (w + lact s c w') + d' • s (w + lact s c w') =
        lact s z w + lact s (z * c) w' := by
      rw [lact_mul s z c (hsq w' (hW'sup w' hw'W)), ← lact_add_right]
      rfl
    have horth : QuadraticMap.polar Q (lact s z w) (lact s (z * c) w') = 0 :=
      hFD.orth _ (lact_mem s hsW z hwW) _ (lact_mem s hsW' _ hw'W)
    rw [e, QuadraticMap.map_add (⇑Q) (lact s z w), map_lact hsQ hτ z (hsq w (hWsup w hwW)),
      map_lact hsQ hτ _ (hsq w' (hW'sup w' hw'W)), map_mul, hcN, mul_one, hQw', horth, add_zero]
    linear_combination (QuadraticAlgebra.norm z * Q w) * h2K
  · intro c' d' h
    have hWpart : c' • w + d' • s w ∈ W := W.add_mem (W.smul_mem c' hwW) (W.smul_mem d' (hsW w hwW))
    have hW'part : c' • lact s c w' + d' • s (lact s c w') ∈ W' :=
      W'.add_mem (W'.smul_mem c' hcw'W) (W'.smul_mem d' (hsW' _ hcw'W))
    have e : c' • w + d' • s w = -(c' • lact s c w' + d' • s (lact s c w')) := by
      rw [eq_neg_iff_add_eq_zero, ← h, map_add]
      module
    have h0 := hdisj _ hWpart (e ▸ W'.neg_mem hW'part)
    exact hindW c' d' h0
  · have e1 : G (lact s c w') = lact s (l₁ * c) w' := by
      rw [semi_lact hGs hGc hστ, hGw', ← lact_mul s _ _ (hsq w' (hW'sup w' hw'W)), ← hφ, hc, hγ]
      congr 1
      field_simp
    rw [map_add, hGw, e1, lact_mul s _ _ (hsq w' (hW'sup w' hw'W)), ← lact_add_right]
    rfl

end Line

end OrthBstarOdd

end CFSG.StandardType
