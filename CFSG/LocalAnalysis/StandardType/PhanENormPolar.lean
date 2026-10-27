module

public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Norm

variable {K : Type*} [Field K] (σ : K ≃+* K) {V : Type*} [AddCommGroup V] [Module K V]

private lemma q2cS3p_exists_smul_of_ker_le {f g : V →ₗ[K] K} (hf : f ≠ 0)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : ∃ c : K, g = c • f := by
  have hex : ∃ u, f u ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hf (LinearMap.ext fun u => by simpa using hnone u)
  obtain ⟨u, hu⟩ := hex
  refine ⟨g u / f u, ?_⟩
  apply LinearMap.ext
  intro v
  have hmem : v - (f v / f u) • u ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp [hu]
    ring
  have hgmem : g (v - (f v / f u) • u) = 0 := by
    simpa [LinearMap.mem_ker] using h hmem
  simp only [map_sub, map_smul, smul_eq_mul, LinearMap.smul_apply] at hgmem ⊢
  field_simp [hu] at hgmem ⊢
  ring_nf at hgmem ⊢
  linear_combination hgmem

private lemma q2cS3p_smul_apply_eq_zero (hσ : σ ^ 2 = 1)
    {h : V →ₛₗ[σ.toRingHom] V →ₗ[K] K} (hnd : h.Nondegenerate) {x x' : V} {c c' : K}
    (hind : LinearIndependent K ![x, x'])
    (hzero : ∀ y, c * h x y + c' * h x' y = 0) : c = 0 ∧ c' = 0 := by
  have hσσ : ∀ a : K, σ (σ a) = a := by
    intro a
    simpa [pow_two] using congrArg (fun e : K ≃+* K => e a) hσ
  have hz : ∀ y, h (σ.symm c • x + σ.symm c' • x') y = 0 := by
    intro y
    rw [h.map_add, h.map_smulₛₗ, h.map_smulₛₗ]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [show σ.toRingHom (σ.symm c) = c from RingEquiv.apply_symm_apply σ c,
      show σ.toRingHom (σ.symm c') = c' from RingEquiv.apply_symm_apply σ c']
    exact hzero y
  have hz0 : σ.symm c • x + σ.symm c' • x' = 0 := hnd.1 _ hz
  obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp hind) (σ.symm c) (σ.symm c') hz0
  exact ⟨by simpa using congrArg σ h1, by simpa using congrArg σ h2⟩

theorem isRefl_of_perp_perp {h : V →ₛₗ[σ.toRingHom] V →ₗ[K] K}
    (hperp : ∀ U : Submodule K V, (U.orthogonalBilin h).orthogonalBilin h = U) : h.IsRefl := by
  intro x y hxy
  have hy : y ∈ (Submodule.span K {x}).orthogonalBilin h := by
    rw [Submodule.mem_orthogonalBilin_span]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hxy
  have hxmem : x ∈ ((Submodule.span K {x}).orthogonalBilin h).orthogonalBilin h := by
    rw [hperp (Submodule.span K {x})]
    exact Submodule.mem_span_singleton_self x
  exact hxmem y hy

theorem exists_const_of_isRefl [Nontrivial V] (hσ : σ ^ 2 = 1)
    {h : V →ₛₗ[σ.toRingHom] V →ₗ[K] K} (hnd : h.Nondegenerate) (hrefl : h.IsRefl) :
    ∃ c : K, c ≠ 0 ∧ σ c * c = 1 ∧ ∀ x y, σ (h y x) = c * h x y := by
  have hσσ : ∀ a : K, σ (σ a) = a := by
    intro a
    simpa [pow_two] using congrArg (fun e : K ≃+* K => e a) hσ
  let g : V → Module.Dual K V := fun x =>
    { toFun := fun y => σ (h y x)
      map_add' := fun y y' => by
        rw [h.map_add]
        simp only [LinearMap.add_apply, map_add]
      map_smul' := fun a y => by
        change σ (h (a • y) x) = a * σ (h y x)
        have hstep : h (a • y) x = σ a * h y x := by
          rw [h.map_smulₛₗ, LinearMap.smul_apply]
          rfl
        rw [hstep, map_mul, hσσ] }
  have hg : ∀ x y, g x y = σ (h y x) := fun x y => rfl
  have h_add : ∀ x x' : V, h (x + x') = h x + h x' := fun x x' => h.map_add x x'
  have h_smul : ∀ (a : K) (x : V), h (a • x) = σ a • h x :=
    fun a x => h.map_smulₛₗ a x
  have hPsg : ∀ (a : K) (x : V), g (a • x) = σ a • g x := by
    intro a x
    ext y
    simp only [hg, LinearMap.smul_apply, smul_eq_mul]
    rw [show h y (a • x) = a * h y x by rw [map_smul, smul_eq_mul], map_mul]
  have hPadd : ∀ x x' : V, g (x + x') = g x + g x' := by
    intro x x'
    ext y
    simp only [hg, LinearMap.add_apply]
    rw [show h y (x + x') = h y x + h y x' by rw [map_add], map_add]
  have hfne : ∀ x : V, x ≠ 0 → h x ≠ 0 := by
    intro x hx h0
    exact hx (hnd.1 x fun y => by
      have := congrArg (fun φ : V →ₗ[K] K => φ y) h0
      simpa using this)
  have hker : ∀ x : V, LinearMap.ker (h x) ≤ LinearMap.ker (g x) := by
    intro x y hy
    rw [LinearMap.mem_ker] at hy ⊢
    rw [hg, hrefl x y hy, map_zero]
  let P : K → V → Prop := fun c x => g x = c • h x
  have hex : ∀ x : V, x ≠ 0 → ∃ c : K, P c x :=
    fun x hx => q2cS3p_exists_smul_of_ker_le (hfne x hx) (hker x)
  have hPuniq : ∀ (c c' : K) (x : V), P c x → P c' x → h x ≠ 0 → c = c' := by
    intro c c' x hc hc' hx
    have hthis : c • h x = c' • h x := hc.symm.trans hc'
    have h0 : (c - c') • h x = 0 := by
      rw [sub_smul c c' (h x), hthis, sub_self]
    rcases smul_eq_zero.mp h0 with hh | hh
    · exact sub_eq_zero.mp hh
    · exact absurd hh hx
  have hPscalar : ∀ (c : K) (x : V) (a : K), P c x → P c (a • x) := by
    intro c x a hc
    show g (a • x) = c • h (a • x)
    rw [hPsg, hc, h_smul, smul_comm]
  have hPsum : ∀ (c c' d : K) (x x' : V), P c x → P c' x' → P d (x + x') →
      LinearIndependent K ![x, x'] → c = d ∧ c' = d := by
    intro c c' d x x' hcx hcx' hdx hind
    have e1 : d • h (x + x') = c • h x + c' • h x' := by
      rw [← hdx, hPadd, hcx, hcx']
    have e2 : d • h (x + x') = d • h x + d • h x' := by rw [h_add, smul_add]
    have e3 : c • h x + c' • h x' = d • h x + d • h x' := e1.symm.trans e2
    have hpt : ∀ y, (c - d) * h x y + (c' - d) * h x' y = 0 := by
      intro y
      have hval := congrArg (fun φ : Module.Dual K V => φ y) e3
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hval
      linear_combination hval
    obtain ⟨h1, h2⟩ := q2cS3p_smul_apply_eq_zero σ hσ hnd hind hpt
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨c₀, hc₀⟩ := hex x₀ hx₀
  have hc₀ne : c₀ ≠ 0 := by
    intro h0
    apply hx₀
    apply hnd.2
    intro y
    have hy := congrArg (fun φ : Module.Dual K V => φ y) hc₀
    simp only [hg, LinearMap.smul_apply, smul_eq_mul, h0, zero_mul] at hy
    exact (map_eq_zero σ).mp hy
  have hcoef : ∀ x : V, x ≠ 0 → P c₀ x := by
    intro x hx
    obtain ⟨cx, hcx⟩ := hex x hx
    have hcx_eq : cx = c₀ := by
      by_cases hdep : ∃ a : K, a • x = x₀
      · obtain ⟨a, ha⟩ := hdep
        have h1 : P cx (a • x) := hPscalar cx x a hcx
        rw [ha] at h1
        exact hPuniq cx c₀ x₀ h1 hc₀ (hfne x₀ hx₀)
      · have hind : LinearIndependent K ![x, x₀] := by
          rw [LinearIndependent.pair_iff' hx]
          exact fun a ha => hdep ⟨a, ha⟩
        have hsum0 : x + x₀ ≠ 0 := by
          intro h0
          exact one_ne_zero ((LinearIndependent.pair_iff.mp hind) 1 1 (by simpa using h0)).1
        obtain ⟨d, hd⟩ := hex (x + x₀) hsum0
        obtain ⟨h1, h2⟩ := hPsum cx c₀ d x x₀ hcx hc₀ hd hind
        exact h1.trans h2.symm
    rwa [hcx_eq] at hcx
  have hid : ∀ a b : V, σ (h b a) = c₀ * h a b := by
    intro a b
    by_cases ha : a = 0
    · subst ha
      have hb0 : (h b) 0 = 0 := map_zero (h b)
      have h0b : (h 0) b = 0 := by rw [map_zero h, LinearMap.zero_apply]
      rw [hb0, h0b, map_zero, mul_zero]
    · have hthis := congrArg (fun φ : Module.Dual K V => φ b) (hcoef a ha)
      simpa [hg, LinearMap.smul_apply, smul_eq_mul] using hthis
  refine ⟨c₀, hc₀ne, ?_, hid⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (hnd.1 x h)
  have h1 : h x y = (σ c₀ * c₀) * h x y := by
    calc h x y = σ (σ (h x y)) := (hσσ _).symm
      _ = σ (c₀ * h y x) := by rw [hid y x]
      _ = σ c₀ * σ (h y x) := map_mul σ c₀ (h y x)
      _ = σ c₀ * (c₀ * h x y) := by rw [hid x y]
      _ = (σ c₀ * c₀) * h x y := by ring
  exact mul_right_cancel₀ hy (by rw [one_mul]; exact h1.symm)

theorem exists_smul_isSymm [Finite K] [Nontrivial V] (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    {h : V →ₛₗ[σ.toRingHom] V →ₗ[K] K} (hnd : h.Nondegenerate) (hrefl : h.IsRefl) :
    ∃ l : K, l ≠ 0 ∧ ∀ x y, σ (l * h y x) = l * h x y := by
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_const_of_isRefl σ hσ hnd hrefl
  obtain ⟨b, hb⟩ := CFSG.ComponentClassification.CatalogueBUnitaryNorm.exists_norm_one_ratio
    σ hσ hne (Units.mk0 c hc0) (by simpa using hc1)
  refine ⟨(b : K), b.ne_zero, fun x y => ?_⟩
  have hb' : (b : K) = c * σ (b : K) := by
    have hden : σ (b : K) ≠ 0 := (map_ne_zero σ).mpr b.ne_zero
    rw [div_eq_iff hden] at hb
    simpa using hb
  rw [map_mul, hc2 x y]
  conv_rhs => rw [hb']
  ring

theorem exists_coord_herm [Finite K] [FiniteDimensional K V] [Nontrivial V] (hσ : σ ^ 2 = 1)
    (hne : σ ≠ 1) {h : V →ₛₗ[σ.toRingHom] V →ₗ[K] K} (hnd : h.Nondegenerate)
    (hrefl : h.IsRefl) :
    ∃ (e : V ≃ₗ[K] (Fin (Module.finrank K V) → K)) (l : K), l ≠ 0 ∧
      ∀ x y, CFSG.ClassicalGroups.Unitary.herm σ (e x) (e y) = l * h x y := by
  obtain ⟨l, hl0, hl⟩ := exists_smul_isSymm σ hσ hne hnd hrefl
  let H : V →ₛₗ[σ.toRingHom] V →ₗ[K] K := l • h
  have hH : ∀ x y, H x y = l * h x y := fun x y => rfl
  have hHsym : H.IsSymm := by
    rw [LinearMap.isSymm_def]
    intro x y
    show σ (l * h x y) = l * h y x
    exact hl y x
  have hHnd : H.Nondegenerate := by
    constructor
    · intro x hx
      apply hnd.1 x
      intro y
      have hthis := hx y
      rw [hH x y] at hthis
      exact (mul_eq_zero.mp hthis).resolve_left hl0
    · intro y hy
      apply hnd.2 y
      intro x
      have hthis := hy x
      rw [hH x y] at hthis
      exact (mul_eq_zero.mp hthis).resolve_left hl0
  obtain ⟨e, he⟩ := CFSG.ComponentClassification.CatalogueBHermitian.exists_coordinate_isometry
    H hHsym hHnd hσ hne
  exact ⟨e, l, hl0, fun x y => by rw [he x y, hH x y]⟩

theorem exists_coord_perp [Finite K] (hσ : σ ^ 2 = 1) (hne : σ ≠ 1) {n : ℕ} (hn : 0 < n)
    {h : (Fin n → K) →ₛₗ[σ.toRingHom] (Fin n → K) →ₗ[K] K} (hnd : h.Nondegenerate)
    (hperp : ∀ U : Submodule K (Fin n → K),
      (U.orthogonalBilin h).orthogonalBilin h = U) :
    ∃ e : (Fin n → K) ≃ₗ[K] (Fin n → K), ∀ (U : Submodule K (Fin n → K)) (v : Fin n → K),
      v ∈ U.orthogonalBilin h ↔ ∀ u ∈ U, CFSG.ClassicalGroups.Unitary.herm σ (e u) (e v) = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Fin n → K) := Function.nontrivial
  have hrefl : h.IsRefl := isRefl_of_perp_perp σ hperp
  obtain ⟨e, l, hl0, he⟩ := exists_coord_herm σ hσ hne hnd hrefl
  have hfin : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  let φ : Fin (Module.finrank K (Fin n → K)) ≃ Fin n := finCongr hfin
  let e' : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    e.trans (LinearEquiv.funCongrLeft K K φ).symm
  have he' : ∀ x y, CFSG.ClassicalGroups.Unitary.herm σ (e' x) (e' y) = l * h x y := by
    intro x y
    have hcongr : CFSG.ClassicalGroups.Unitary.herm σ (e' x) (e' y) =
        CFSG.ClassicalGroups.Unitary.herm σ (e x) (e y) := by
      simp only [e', LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_symm,
        LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
        CFSG.ClassicalGroups.Unitary.herm]
      exact Equiv.sum_comp φ.symm (fun j => σ ((e x) j) * (e y) j)
    rw [hcongr, he x y]
  refine ⟨e', fun U v => ?_⟩
  rw [Submodule.mem_orthogonalBilin]
  constructor
  · intro hv u hu
    rw [he' u v, hv u hu, mul_zero]
  · intro hv u hu
    have hz := hv u hu
    rw [he' u v] at hz
    exact (mul_eq_zero.mp hz).resolve_left hl0

end CFSG.ClassicalInvolution.Phan.PhanE.Norm
