module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.SzN28

theorem split_of_dual {K : Type*} [Group K] {Vt Vh : Type*} [AddCommGroup Vt] [Module (ZMod 2) Vt]
    [AddCommGroup Vh] [Module (ZMod 2) Vh]
    (ρ : K →* (Vt ≃ₗ[ZMod 2] Vt)) (σ : K →* (Vh ≃ₗ[ZMod 2] Vh)) (π : Vt →ₗ[ZMod 2] Vh)
    (hπ : Function.Surjective π) (hπρ : ∀ k x, π (ρ k x) = σ k (π x))
    (hKZ : ∀ k z, π z = 0 → ρ k z = z) (hker : ∀ k, σ k = 1 → ρ k = 1)
    (Φ : Module.Dual (ZMod 2) Vh ≃ₗ[ZMod 2] Vh)
    (hΦ : ∀ k μ, Φ (μ ∘ₗ ((σ k⁻¹ : Vh ≃ₗ[ZMod 2] Vh) : Vh →ₗ[ZMod 2] Vh)) = σ k (Φ μ))
    (hfix : ∀ u : Vh, (∀ k, σ k u = u) → u = 0)
    (hcoh : ∀ δ : K → Vh, (∀ k l, δ (k * l) = δ k + σ k (δ l)) → (∀ k, σ k = 1 → δ k = 0) →
      ∃ n, ∀ k, δ k = σ k n - n) :
    (∀ x : Vt, ∃ n ∈ Submodule.span (ZMod 2) {y : Vt | ∃ k, ∃ w, y = ρ k w - w}, π (x - n) = 0) ∧
    ∀ x ∈ Submodule.span (ZMod 2) {y : Vt | ∃ k, ∃ w, y = ρ k w - w}, π x = 0 → x = 0 := by
  classical
  set R : Submodule (ZMod 2) Vt := Submodule.span (ZMod 2) {y : Vt | ∃ k, ∃ w, y = ρ k w - w}
    with hR
  constructor
  ·
    have htop : R.map π = ⊤ := by
      by_contra hne
      obtain ⟨μ, hμ0, hμ⟩ :=
        Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
      have hvan : ∀ x ∈ R.map π, μ x = 0 := fun x hx => by
        have : μ x ∈ (R.map π).map μ := Submodule.mem_map_of_mem hx
        rw [hμ] at this
        simpa using this
      have hfixμ : ∀ k v, μ (σ k v) = μ v := by
        intro k v
        obtain ⟨w, rfl⟩ := hπ v
        have h := hvan (π (ρ k w - w))
          ⟨ρ k w - w, Submodule.subset_span ⟨k, w, rfl⟩, rfl⟩
        rw [map_sub, hπρ, map_sub] at h
        exact sub_eq_zero.1 h
      apply hμ0
      have h0 : Φ μ = 0 := hfix _ fun k => by
        rw [← hΦ]
        have : μ ∘ₗ ((σ k⁻¹ : Vh ≃ₗ[ZMod 2] Vh) : Vh →ₗ[ZMod 2] Vh) = μ :=
          LinearMap.ext fun v => hfixμ k⁻¹ v
        rw [this]
      exact Φ.map_eq_zero_iff.1 h0
    intro x
    have hx : π x ∈ R.map π := by rw [htop]; trivial
    obtain ⟨n, hn, hπn⟩ := hx
    exact ⟨n, hn, by rw [map_sub, hπn, sub_self]⟩
  · intro z hzR hπz
    by_contra hz0
    obtain ⟨l₀, hl₀⟩ : ∃ l₀ : Module.Dual (ZMod 2) Vt, l₀ z ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hz0 ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) z).1 hall)
    have hρmul : ∀ (a b : K) (x : Vt), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
      rw [map_mul]; rfl
    have hσmul : ∀ (a b : K) (x : Vh), σ (a * b) x = σ a (σ b x) := fun a b x => by
      rw [map_mul]; rfl
    have hdesc : ∀ k : K, ∃ ν : Module.Dual (ZMod 2) Vh,
        ν ∘ₗ π = l₀ ∘ₗ ((ρ k⁻¹ : Vt ≃ₗ[ZMod 2] Vt) : Vt →ₗ[ZMod 2] Vt) - l₀ := by
      intro k
      have hmem : l₀ ∘ₗ ((ρ k⁻¹ : Vt ≃ₗ[ZMod 2] Vt) : Vt →ₗ[ZMod 2] Vt) - l₀ ∈
          (LinearMap.ker π).dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        intro z' hz'
        rw [LinearMap.mem_ker] at hz'
        rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hKZ k⁻¹ z' hz',
          sub_self]
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective π hπ] at hmem
      obtain ⟨ν, hν⟩ := hmem
      exact ⟨ν, by rw [← hν]; rfl⟩
    choose ν hν using hdesc
    have hνapp : ∀ k x, ν k (π x) = l₀ (ρ k⁻¹ x) - l₀ x := fun k x => by
      have := congrArg (fun f : Module.Dual (ZMod 2) Vt => f x) (hν k)
      simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearEquiv.coe_coe] using this
    have hνcoc : ∀ k l, ν (k * l) =
        ν k + ν l ∘ₗ ((σ k⁻¹ : Vh ≃ₗ[ZMod 2] Vh) : Vh →ₗ[ZMod 2] Vh) := by
      intro k l
      apply LinearMap.ext
      intro v
      obtain ⟨x, rfl⟩ := hπ v
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, ← hπρ, hνapp, hνapp,
        hνapp, mul_inv_rev, hρmul]
      abel
    have hνker : ∀ k, σ k = 1 → ν k = 0 := by
      intro k hk
      have hρk : ρ k⁻¹ = 1 := by
        rw [map_inv, hker k hk, inv_one]
      apply LinearMap.ext
      intro v
      obtain ⟨x, rfl⟩ := hπ v
      rw [hνapp, hρk]
      simp
    obtain ⟨n, hn⟩ := hcoh (fun k => Φ (ν k))
      (fun k l => by
        rw [hνcoc, map_add, hΦ])
      (fun k hk => by rw [hνker k hk, map_zero])
    set ν₁ : Module.Dual (ZMod 2) Vh := Φ.symm n with hν₁
    have hνk : ∀ k, ν k = ν₁ ∘ₗ ((σ k⁻¹ : Vh ≃ₗ[ZMod 2] Vh) : Vh →ₗ[ZMod 2] Vh) - ν₁ := by
      intro k
      apply Φ.injective
      rw [hn k, map_sub, hΦ, hν₁, LinearEquiv.apply_symm_apply]
    have hlfix : ∀ k x, (l₀ - ν₁ ∘ₗ π) (ρ k x) = (l₀ - ν₁ ∘ₗ π) x := by
      intro k x
      have h1 := hνapp k⁻¹ x
      have h2 : ν k⁻¹ (π x) = ν₁ (σ k⁻¹⁻¹ (π x)) - ν₁ (π x) := by
        rw [hνk k⁻¹]
        rfl
      rw [inv_inv, ← hπρ] at h2
      rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
      rw [inv_inv] at h1
      have h3 : l₀ (ρ k x) - l₀ x = ν₁ (π (ρ k x)) - ν₁ (π x) := h1.symm.trans h2
      calc l₀ (ρ k x) - ν₁ (π (ρ k x)) = (l₀ (ρ k x) - l₀ x) - (ν₁ (π (ρ k x)) - ν₁ (π x)) +
            (l₀ x - ν₁ (π x)) := by abel
        _ = l₀ x - ν₁ (π x) := by rw [h3, sub_self, zero_add]
    have hz1 : (l₀ - ν₁ ∘ₗ π) z = 0 := by
      refine Submodule.span_induction (p := fun x _ => (l₀ - ν₁ ∘ₗ π) x = 0) ?_ ?_ ?_ ?_ hzR
      · rintro y ⟨k, w, rfl⟩
        rw [map_sub, hlfix k w, sub_self]
      · exact map_zero _
      · intro a b _ _ ha hb
        rw [map_add, ha, hb, add_zero]
      · intro c a _ ha
        rw [map_smul, ha, smul_zero]
    apply hl₀
    have h4 : (l₀ - ν₁ ∘ₗ π) z = l₀ z := by
      rw [LinearMap.sub_apply, LinearMap.comp_apply, hπz, map_zero, sub_zero]
    rw [← h4, hz1]

theorem ker_eq_bot_of_decomp {Θ : Type*} [Group Θ] {Vt Vh : Type*} [AddCommGroup Vt]
    [Module (ZMod 2) Vt] [AddCommGroup Vh] [Module (ZMod 2) Vh]
    (ρ : Θ →* (Vt ≃ₗ[ZMod 2] Vt)) (π : Vt →ₗ[ZMod 2] Vh) (K : Subgroup Θ) (hKn : K.Normal)
    (hdec : ∀ x : Vt, ∃ n ∈ Submodule.span (ZMod 2) {y : Vt | ∃ k : K, ∃ w : Vt, y = ρ k w - w},
      π (x - n) = 0)
    (huniq : ∀ x ∈ Submodule.span (ZMod 2) {y : Vt | ∃ k : K, ∃ w : Vt, y = ρ k w - w},
      π x = 0 → x = 0)
    (Y : Subgroup Θ) (hYZ : ∀ y ∈ Y, ∀ z : Vt, π z = 0 → ρ y z = z) (v : Vt)
    (hv : v ∈ Submodule.span (ZMod 2) {x : Vt | ∃ y ∈ Y, ∃ w : Vt, x = ρ y w - w})
    (hgen : Submodule.span (ZMod 2) (Set.range fun θ : Θ => ρ θ v) = ⊤) :
    ∀ z : Vt, π z = 0 → z = 0 := by
  set N := Submodule.span (ZMod 2) {y : Vt | ∃ k : K, ∃ w : Vt, y = ρ k w - w} with hN
  have hinv : ∀ θ : Θ, ∀ x ∈ N, ρ θ x ∈ N := by
    intro θ x hx
    have hle : N ≤ N.comap (ρ θ : Vt →ₗ[ZMod 2] Vt) := by
      refine Submodule.span_le.mpr ?_
      rintro y ⟨k, w, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Submodule.subset_span ⟨⟨θ * (k : Θ) * θ⁻¹, hKn.conj_mem _ k.2 θ⟩, ρ θ w, ?_⟩
      simp [map_mul]
    exact hle hx
  have hgenN : ∀ y ∈ Y, ∀ w, ρ y w - w ∈ N := by
    intro y hy w
    obtain ⟨n, hn, hπn⟩ := hdec w
    have hc : ρ y (w - n) = w - n := hYZ y hy _ hπn
    have : ρ y w - w = ρ y n - n := by
      rw [map_sub] at hc
      have h2 : ρ y w - ρ y n = w - n := hc
      calc ρ y w - w = (ρ y w - ρ y n) - (w - n) + (ρ y n - n) := by abel
        _ = ρ y n - n := by rw [h2, sub_self, zero_add]
    rw [this]
    exact N.sub_mem (hinv y n hn) hn
  have hvN : v ∈ N := by
    have : Submodule.span (ZMod 2) {x : Vt | ∃ y ∈ Y, ∃ w : Vt, x = ρ y w - w} ≤ N := by
      refine Submodule.span_le.mpr ?_
      rintro x ⟨y, hy, w, rfl⟩
      exact hgenN y hy w
    exact this hv
  have hNtop : N = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨θ, rfl⟩
    exact hinv θ v hvN
  intro z hz
  exact huniq z (by rw [hNtop]; trivial) hz

end CFSG.Quasithin.SzN28
