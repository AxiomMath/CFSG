module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU2

public section

namespace CFSG.StandardType.TraceFrame

open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LocalAnalysis.ComponentInitial Matrix

lemma frob_trace_sum {K M : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] (hK : Nat.card K = 2) {τ : M ≃+* M} (hτ : ∀ y, τ (τ y) = y) {n : ℕ}
    (i : Fin n) (d d' : Fin n → M) :
    ∑ j, Algebra.trace K M
        (τ (Function.update d i (τ (d i)) j) * Function.update d' i (τ (d' i)) j) =
      ∑ j, Algebra.trace K M (τ (d j) * d' j) := by
  rw [Fintype.sum_eq_add_sum_compl i, Fintype.sum_eq_add_sum_compl i]
  congr 1
  · rw [Function.update_self, Function.update_self, hτ]
    rw [← trace_tau hK (d i * τ (d' i)), map_mul, hτ]
  · refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_compl, Finset.mem_singleton] at hj
    rw [Function.update_of_ne hj, Function.update_of_ne hj]

lemma frobUnit_mem {K M V U : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {τ : M ≃+* M} (hK : Nat.card K = 2) (hτ : ∀ y, τ (τ y) = y) {n : ℕ}
    {B : LinearMap.BilinForm K V} {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w')))
    (i : Fin n) :
    frobUnit hK hτ Φ i ∈ sesqUnitaryGroup B := by
  rw [mem_sesqUnitaryGroup]
  intro x y
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective x
  obtain ⟨⟨d', w'⟩, rfl⟩ := Φ.surjective y
  simp only [coe_frobUnit, LinearEquiv.coe_coe]
  calc
    B (frobEquivV hK hτ Φ i (Φ (d, w))) (frobEquivV hK hτ Φ i (Φ (d', w')))
        = B (Φ (Function.update d i (τ (d i)), w))
            (Φ (Function.update d' i (τ (d' i)), w')) := by
          rw [frobEquivV_apply, frobEquivV_apply]
    _ = ∑ j, Algebra.trace K M
          (τ (Function.update d i (τ (d i)) j) * Function.update d' i (τ (d' i)) j) +
          B (Φ (0, w)) (Φ (0, w')) := hB _ _ _ _
    _ = ∑ j, Algebra.trace K M (τ (d j) * d' j) + B (Φ (0, w)) (Φ (0, w')) := by
          congr 1
          exact frob_trace_sum hK hτ i d d'
    _ = B (Φ (d, w)) (Φ (d', w')) := (hB d d' w w').symm
lemma frob_diag_vec {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (_hK : Nat.card K = 2) {τ : M ≃+* M} (hτ : ∀ y, τ (τ y) = y) {n : ℕ}
    {A A' : Matrix (Fin n) (Fin n) M} {i : Fin n}
    (hA : ∀ j k, j ≠ k → A j k = 0) (hA' : ∀ j k, j ≠ k → A' j k = 0)
    (hii : A' i i = τ (A i i)) (hjj : ∀ j, j ≠ i → A' j j = A j j)
    (d : Fin n → M) :
    Function.update (A *ᵥ Function.update d i (τ (d i))) i
        (τ ((A *ᵥ Function.update d i (τ (d i))) i)) = A' *ᵥ d := by
  have hAeq : A = Matrix.diagonal fun j => A j j := by
    ext j k
    by_cases h : j = k
    · subst h; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h]; exact hA j k h
  have hA'eq : A' = Matrix.diagonal fun j => A' j j := by
    ext j k
    by_cases h : j = k
    · subst h; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h]; exact hA' j k h
  rw [hAeq, hA'eq]
  ext j
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self, Matrix.mulVec_diagonal, map_mul, hτ]
    rw [hii]
  · simp only [Function.update_of_ne hj, Matrix.mulVec_diagonal]
    rw [hjj j hj]

lemma frob_trivial_vec {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    {τ : M ≃+* M} (hτ : ∀ y, τ (τ y) = y) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) M} {i : Fin n}
    (hrow : ∀ j, j ≠ i → A i j = 0) (hcol : ∀ j, j ≠ i → A j i = 0)
    (hii : A i i = 1) (d : Fin n → M) :
    Function.update (A *ᵥ Function.update d i (τ (d i))) i
        (τ ((A *ᵥ Function.update d i (τ (d i))) i)) = A *ᵥ d := by
  have hAi : ∀ x : Fin n → M, (A *ᵥ x) i = x i := by
    intro x
    rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single i]
    · rw [hii, one_mul]
    · intro j hj
      rw [hrow j hj, zero_mul]
  ext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, hAi, Function.update_self, hτ, hAi]
  · rw [Function.update_of_ne hj]
    rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl ?_
    intro k _
    by_cases hki : k = i
    · subst hki
      rw [Function.update_self, hcol j hj]
      simp
    · rw [Function.update_of_ne hki]

lemma frobUnit_apply {K M V U : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {τ : M ≃+* M} (hK : Nat.card K = 2) (hτ : ∀ y, τ (τ y) = y) {n : ℕ}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (i : Fin n)
    (d : Fin n → M) (w : U) :
    ((frobUnit hK hτ Φ i : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
      (Φ (d, w)) = Φ (Function.update d i (τ (d i)), w) := by
  rw [coe_frobUnit_apply]
  simp only [frobEquivV_apply]

section Centralizer

variable {K M V U : Type} [Field K] [Field M] [Algebra K M]
  [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
  {n : ℕ} {B : LinearMap.BilinForm K V} {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
  {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}

@[expose] noncomputable def sesqLin (g : ↥(sesqUnitaryGroup B)) : V →ₗ[K] V :=
  ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)

lemma sesqLin_comm {g s : ↥(sesqUnitaryGroup B)} (h : g * s = s * g) (v : V) :
    sesqLin g (sesqLin s v) = sesqLin s (sesqLin g v) := by
  have h' := congrArg (fun u : ↥(sesqUnitaryGroup B) =>
    ((u : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) h
  have h'' := congrArg (fun f : V →ₗ[K] V => f v) h'
  simpa [sesqLin, Units.val_mul, Module.End.mul_apply] using h''

lemma sesq_fixed_of_eq {s : ↥(sesqUnitaryGroup B)} {c : M} (hc : c ^ 2 ≠ c)
    (hs : ∀ d w, sesqLin s (Φ (d, w)) = Φ (c • d, w)) {v : V}
    (hv : sesqLin s v = v) : ∃ u : U, v = Φ (0, u) := by
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hc (by rw [one_pow])
  have hd : c • d = d := by
    have h : Φ (c • d, w) = Φ (d, w) := by rw [← hs, hv]
    exact (Prod.ext_iff.mp (Φ.injective h)).1
  have hzero : ∀ i, d i = 0 := by
    intro i
    have hdi : c * d i = d i := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hd i
    have h0 : (c - 1) * d i = 0 := by
      rw [sub_mul, one_mul, hdi, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc1)
  refine ⟨w, ?_⟩
  rw [show d = 0 from funext hzero]

lemma sesq_fixes_inr {s g : ↥(sesqUnitaryGroup B)} {c : M}
    (hs : ∀ d w, sesqLin s (Φ (d, w)) = Φ (c • d, w))
    (hcomm : g * s = s * g) (w : U) :
    sesqLin s (sesqLin g (Φ (0, w))) = sesqLin g (Φ (0, w)) := by
  rw [← sesqLin_comm hcomm]
  rw [hs]
  simp

lemma sesq_inl_maps_inl {s g : ↥(sesqUnitaryGroup B)} {c : M}
    (hc : c ^ 2 ≠ c) (hs : ∀ d w, sesqLin s (Φ (d, w)) = Φ (c • d, w))
    (hcomm : g * s = s * g) (d : Fin n → M) :
    ∃ e : Fin n → M, sesqLin g (Φ (d, 0)) = Φ (e, 0) := by
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hc (by rw [one_pow])
  have hcm1 : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  let e : Fin n → M := (c - 1)⁻¹ • d
  have hsplit : sesqLin s (Φ (e, 0)) - Φ (e, 0) = Φ (d, 0) := by
    rw [hs]
    have hsub : (c • e, (0 : U)) - (e, 0) = (d, 0) := by
      ext i
      · change c * e i - e i = d i
        have hce : c * e i - e i = (c - 1) * e i := by ring
        rw [hce]
        simp only [e, Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_inv_cancel₀ hcm1, one_mul]
      · simp
    calc
      Φ (c • e, (0 : U)) - Φ (e, 0) = Φ ((c • e, (0 : U)) - (e, 0)) :=
        (map_sub Φ _ _).symm
      _ = Φ (d, 0) := by rw [hsub]
  have hGs : sesqLin g (Φ (d, 0)) =
      sesqLin s (sesqLin g (Φ (e, 0))) - sesqLin g (Φ (e, 0)) := by
    rw [← hsplit, map_sub, ← sesqLin_comm hcomm]
  obtain ⟨⟨e', u'⟩, hGu⟩ := Φ.surjective (sesqLin g (Φ (e, 0)))
  refine ⟨(c - 1) • e', ?_⟩
  rw [hGs, ← hGu, hs]
  have hsub : (c • e', u') - (e', u') = ((c - 1) • e', (0 : U)) := by
    ext i
    · change c * e' i - e' i = (c - 1) * e' i
      ring
    · simp
  calc
    Φ (c • e', u') - Φ (e', u') = Φ ((c • e', u') - (e', u')) :=
      (map_sub Φ _ _).symm
    _ = Φ ((c - 1) • e', (0 : U)) := by rw [hsub]

lemma sesq_exists_form [Finite K] [Finite M] (hK : Nat.card K = 2) (hM : Nat.card M = 4)
    {s g : ↥(sesqUnitaryGroup B)} {c : M} (hc : c ^ 2 ≠ c)
    (hs : ∀ d w, sesqLin s (Φ (d, w)) = Φ (c • d, w))
    (hcomm : g * s = s * g) :
    ∃ (g' : (Fin n → M) →ₗ[K] (Fin n → M)) (g₀ : U →ₗ[K] U),
      (∀ d w, sesqLin g (Φ (d, w)) = Φ (g' d, g₀ w)) ∧
      (∀ (m : M) (d : Fin n → M), g' (m • d) = m • g' d) := by
  let ι : (Fin n → M) →ₗ[K] V := Φ.toLinearMap.comp (LinearMap.inl K (Fin n → M) U)
  let κ : U →ₗ[K] V := Φ.toLinearMap.comp (LinearMap.inr K (Fin n → M) U)
  have hι : Function.Injective ι := by
    intro x y h
    have h' : Φ (x, (0 : U)) = Φ (y, 0) := by simpa [ι] using h
    exact (Prod.ext_iff.mp (Φ.injective h')).1
  have hκ : Function.Injective κ := by
    intro x y h
    have h' : Φ ((0 : Fin n → M), x) = Φ (0, y) := by simpa [κ] using h
    exact (Prod.ext_iff.mp (Φ.injective h')).2
  let eι : (Fin n → M) ≃ₗ[K] (LinearMap.range ι) := LinearEquiv.ofInjective ι hι
  let eκ : U ≃ₗ[K] (LinearMap.range κ) := LinearEquiv.ofInjective κ hκ
  have hGV : ∀ x ∈ LinearMap.range ι, sesqLin g x ∈ LinearMap.range ι := by
    intro x hx
    obtain ⟨d, rfl⟩ := hx
    obtain ⟨e, he⟩ := sesq_inl_maps_inl hc hs hcomm d
    exact ⟨e, by simpa [ι] using he.symm⟩
  have hGW : ∀ x ∈ LinearMap.range κ, sesqLin g x ∈ LinearMap.range κ := by
    intro x hx
    obtain ⟨w, rfl⟩ := hx
    have hfix := sesq_fixes_inr hs hcomm w
    obtain ⟨u, hu⟩ := sesq_fixed_of_eq hc hs hfix
    exact ⟨u, by simpa [κ] using hu.symm⟩
  let G₀ : LinearMap.range ι →ₗ[K] LinearMap.range ι :=
    ((sesqLin g).domRestrict (LinearMap.range ι)).codRestrict (LinearMap.range ι)
      (fun x => hGV x.val x.2)
  let G₁ : LinearMap.range κ →ₗ[K] LinearMap.range κ :=
    ((sesqLin g).domRestrict (LinearMap.range κ)).codRestrict (LinearMap.range κ)
      (fun x => hGW x.val x.2)
  let g' : (Fin n → M) →ₗ[K] (Fin n → M) :=
    (eι.symm : LinearMap.range ι →ₗ[K] (Fin n → M)).comp
      (G₀.comp (eι : (Fin n → M) →ₗ[K] LinearMap.range ι))
  let g₀ : U →ₗ[K] U :=
    (eκ.symm : LinearMap.range κ →ₗ[K] U).comp
      (G₁.comp (eκ : U →ₗ[K] LinearMap.range κ))
  have hg' : ∀ d : Fin n → M, Φ (g' d, (0 : U)) = sesqLin g (Φ (d, 0)) := by
    intro d
    have h3 : (eι (g' d)).val = sesqLin g (Φ (d, 0)) := by
      have h4 : eι (g' d) = G₀ (eι d) := by
        change eι (eι.symm (G₀ (eι d))) = G₀ (eι d)
        exact eι.apply_symm_apply _
      rw [h4]
      rfl
    calc
      Φ (g' d, (0 : U)) = ι (g' d) := by simp [ι]
      _ = (eι (g' d)).val := rfl
      _ = sesqLin g (Φ (d, 0)) := h3
  have hg₀ : ∀ w : U, Φ ((0 : Fin n → M), g₀ w) = sesqLin g (Φ (0, w)) := by
    intro w
    have h3 : (eκ (g₀ w)).val = sesqLin g (Φ (0, w)) := by
      have h4 : eκ (g₀ w) = G₁ (eκ w) := by
        change eκ (eκ.symm (G₁ (eκ w))) = G₁ (eκ w)
        exact eκ.apply_symm_apply _
      rw [h4]
      rfl
    calc
      Φ ((0 : Fin n → M), g₀ w) = κ (g₀ w) := by simp [κ]
      _ = (eκ (g₀ w)).val := rfl
      _ = sesqLin g (Φ (0, w)) := h3
  have hform : ∀ d w, sesqLin g (Φ (d, w)) = Φ (g' d, g₀ w) := by
    intro d w
    have hdec : Φ (d, w) = Φ (d, 0) + Φ (0, w) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    calc
      sesqLin g (Φ (d, w)) = sesqLin g (Φ (d, 0) + Φ (0, w)) := by rw [hdec]
      _ = sesqLin g (Φ (d, 0)) + sesqLin g (Φ (0, w)) := map_add _ _ _
      _ = Φ (g' d, 0) + Φ (0, g₀ w) := by rw [← hg' d, ← hg₀ w]
      _ = Φ ((g' d, 0) + ((0 : Fin n → M), g₀ w)) := (map_add Φ _ _).symm
      _ = Φ (g' d, g₀ w) := by congr 1; ext <;> simp
  have hgc : ∀ d, g' (c • d) = c • g' d := by
    intro d
    have heq : Φ (g' (c • d), (0 : U)) = Φ (c • g' d, 0) := by
      calc
        Φ (g' (c • d), (0 : U)) = sesqLin g (Φ (c • d, 0)) := hg' (c • d)
        _ = sesqLin g (sesqLin s (Φ (d, 0))) := by rw [← hs]
        _ = sesqLin s (sesqLin g (Φ (d, 0))) := sesqLin_comm hcomm _
        _ = sesqLin s (Φ (g' d, 0)) := by rw [← hg' d]
        _ = Φ (c • g' d, 0) := hs (g' d) 0
    exact (Prod.ext_iff.mp (Φ.injective heq)).1
  have hm : ∀ (m : M) (d : Fin n → M), g' (m • d) = m • g' d := by
    intro m d
    obtain ⟨a, b, hmab⟩ := exists_eq_algebraMap_add_mul hK hM hc m
    rw [hmab]
    have hsplit : (algebraMap K M a + algebraMap K M b * c) • d =
        a • d + b • (c • d) := by
      ext i
      change (algebraMap K M a + algebraMap K M b * c) • d i =
        a • d i + b • (c • d i)
      rw [smul_eq_mul, Algebra.smul_def, Algebra.smul_def, smul_eq_mul]
      rw [add_mul]
      ring
    have hsplit' : (algebraMap K M a + algebraMap K M b * c) • g' d =
        a • g' d + b • (c • g' d) := by
      ext i
      change (algebraMap K M a + algebraMap K M b * c) • g' d i =
        a • g' d i + b • (c • g' d i)
      rw [smul_eq_mul, Algebra.smul_def, Algebra.smul_def, smul_eq_mul]
      rw [add_mul]
      ring
    rw [hsplit, map_add, map_smul, map_smul, hgc, hsplit']
  exact ⟨g', g₀, hform, hm⟩

lemma sesq_trace_sum [Finite K] [Finite M] {g : ↥(sesqUnitaryGroup B)}
    (hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w')))
    (g' : (Fin n → M) →ₗ[K] (Fin n → M)) (g₀ : U →ₗ[K] U)
    (hm : ∀ (m : M) (d : Fin n → M), g' (m • d) = m • g' d)
    (hform : ∀ d w, sesqLin g (Φ (d, w)) = Φ (g' d, g₀ w))
    (hg_iso : ∀ x y, B (sesqLin g x) (sesqLin g y) = B x y)
    (d d' : Fin n → M) :
    ∑ i, τ (g' d i) * g' d' i = ∑ i, τ (d i) * d' i := by
  have htr : ∀ μ : M, Algebra.trace K M (μ * ∑ i, τ (g' d i) * g' d' i) =
      Algebra.trace K M (μ * ∑ i, τ (d i) * d' i) := by
    intro μ
    have hB00 : B (Φ ((0 : Fin n → M), (0 : U))) (Φ ((0 : Fin n → M), (0 : U))) = 0 := by
      have h0 : Φ ((0 : Fin n → M), (0 : U)) = 0 := by simp
      rw [h0]
      exact map_zero (B 0)
    have hL : B (sesqLin g (Φ (d, 0))) (sesqLin g (Φ (μ • d', 0))) =
        ∑ i, Algebra.trace K M (τ (g' d i) * (μ * g' d' i)) := by
      rw [hform, hform, map_zero, hm, hB, hB00, add_zero]
      simp [Pi.smul_apply, smul_eq_mul]
    have hR : B (Φ (d, 0)) (Φ (μ • d', 0)) =
        ∑ i, Algebra.trace K M (τ (d i) * (μ * d' i)) := by
      rw [hB, hB00, add_zero]
      simp [Pi.smul_apply, smul_eq_mul]
    have hiso := hg_iso (Φ (d, 0)) (Φ (μ • d', 0))
    rw [hL, hR] at hiso
    calc
      Algebra.trace K M (μ * ∑ i, τ (g' d i) * g' d' i)
          = ∑ i, Algebra.trace K M (μ * (τ (g' d i) * g' d' i)) := by
            rw [Finset.mul_sum, map_sum]
      _ = ∑ i, Algebra.trace K M (τ (g' d i) * (μ * g' d' i)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            congr 1
            ring
      _ = ∑ i, Algebra.trace K M (τ (d i) * (μ * d' i)) := hiso
      _ = ∑ i, Algebra.trace K M (μ * (τ (d i) * d' i)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            congr 1
            ring
      _ = Algebra.trace K M (μ * ∑ i, τ (d i) * d' i) := by
            rw [Finset.mul_sum, map_sum]
  have hzero : ∑ i, τ (g' d i) * g' d' i - ∑ i, τ (d i) * d' i = 0 := by
    apply eq_zero_of_trace_mul_eq_zero (K := K)
    intro μ
    rw [mul_sub, map_sub, htr μ, sub_self]
  exact sub_eq_zero.mp hzero

lemma sesq_matrix_identity [Finite K] [Finite M] {g : ↥(sesqUnitaryGroup B)}
    (hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w')))
    (g' : (Fin n → M) →ₗ[K] (Fin n → M)) (g₀ : U →ₗ[K] U)
    (hm : ∀ (m : M) (d : Fin n → M), g' (m • d) = m • g' d)
    (hform : ∀ d w, sesqLin g (Φ (d, w)) = Φ (g' d, g₀ w))
    (hg_iso : ∀ x y, B (sesqLin g x) (sesqLin g y) = B x y)
    (A : Matrix (Fin n) (Fin n) M)
    (hA : ∀ i j, A i j = g' (Pi.single j (1 : M)) i) :
    (A.map τ)ᵀ * A = 1 := by
  ext j k
  change ∑ i, τ (A i j) * A i k = (1 : Matrix (Fin n) (Fin n) M) j k
  rw [Matrix.one_apply]
  have h := sesq_trace_sum hB g' g₀ hm hform hg_iso (Pi.single j 1) (Pi.single k 1)
  simpa [hA, Pi.single_apply, eq_comm] using h

lemma sesq_centralizer_form [Finite K] [Finite M] (hK : Nat.card K = 2) (hM : Nat.card M = 4)
    (hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w')))
    {s g : ↥(sesqUnitaryGroup B)} {c : M} (hc : c ^ 2 ≠ c)
    (hs : ∀ d w, sesqLin s (Φ (d, w)) = Φ (c • d, w))
    (hcomm : g * s = s * g) :
    ∃ (A : ↥(heldGU n M τ hτ)) (g₀ : U →ₗ[K] U), ∀ d w,
      sesqLin g (Φ (d, w)) = Φ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d,
        g₀ w) := by
  obtain ⟨g', g₀, hform, hm⟩ := sesq_exists_form hK hM hc hs hcomm
  let A : Matrix (Fin n) (Fin n) M := fun i j => g' (Pi.single j (1 : M)) i
  have hA : (A.map τ)ᵀ * A = 1 :=
    sesq_matrix_identity hB g' g₀ hm hform (mem_sesqUnitaryGroup.mp g.2) A
      (fun _ _ => rfl)
  have hunit : IsUnit A :=
    (Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_left_inverse hA)
  let Au : GL (Fin n) M := hunit.unit
  have hAu : (Au : Matrix (Fin n) (Fin n) M) = A := IsUnit.unit_spec hunit
  have hheld : Au ∈ heldGU n M τ hτ := by
    rw [mem_heldGU, hAu]
    exact hA
  let A' : ↥(heldGU n M τ hτ) := ⟨Au, hheld⟩
  have hg'eq : ∀ d : Fin n → M, g' d = Au *ᵥ d := by
    intro d
    have hd : d = ∑ j, d j • Pi.single j (1 : M) := by
      rw [← Finset.univ_sum_single d]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finset.sum_apply, Fintype.sum_pi_single]
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    calc
      g' d = g' (∑ j, d j • Pi.single j (1 : M)) := by
        conv_lhs => rw [hd]
      _ = ∑ j, g' (d j • Pi.single j (1 : M)) := map_sum _ _ _
      _ = ∑ j, d j • g' (Pi.single j (1 : M)) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hm]
      _ = Au *ᵥ d := by
        ext i
        rw [Matrix.mulVec, dotProduct, Finset.sum_apply, hAu]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Pi.smul_apply, smul_eq_mul]
        ring
  refine ⟨A', g₀, fun d w => ?_⟩
  rw [hform d w, hg'eq d]
end Centralizer
end CFSG.StandardType.TraceFrame
end
