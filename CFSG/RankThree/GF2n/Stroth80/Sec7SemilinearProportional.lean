module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Proportional
public import CFSG.RankThree.GF2n.Stroth80.Sec7OvoidSemilinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_symm_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (σ : K ≃+* K)
    (ν : V ≃+ V) (hν : ∀ (c : K) (v : V), ν (c • v) = σ c • ν v) (c : K) (v : V) :
    ν.symm (c • v) = σ.symm c • ν.symm v := by
  apply ν.injective
  rw [ν.apply_symm_apply, hν, σ.apply_symm_apply, ν.apply_symm_apply]

def sec7_restrictEquiv {K E : Type*} [Field K] [AddCommGroup E] [Module K E] (ν : E ≃+ E)
    (U : Submodule K E) (hνU : ∀ e, e ∈ U ↔ ν e ∈ U) : U ≃+ U where
  toFun x := ⟨ν (x : E), (hνU (x : E)).mp x.2⟩
  invFun x := ⟨ν.symm (x : E), (hνU (ν.symm (x : E))).mpr (by rw [ν.apply_symm_apply]; exact x.2)⟩
  left_inv x := Subtype.ext (ν.symm_apply_apply (x : E))
  right_inv x := Subtype.ext (ν.apply_symm_apply (x : E))
  map_add' x y := Subtype.ext (map_add ν (x : E) (y : E))

def sec7_transportForm {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (σ : K ≃+* K)
    (ν : V ≃+ V) (hν : ∀ (c : K) (v : V), ν (c • v) = σ c • ν v) (a : K)
    (β : LinearMap.BilinForm K V) : LinearMap.BilinForm K V :=
  LinearMap.mk₂ K (fun x y => a * σ (β (ν.symm x) (ν.symm y)))
    (fun x x' y => by simp only [map_add, LinearMap.add_apply, mul_add])
    (fun c x y => by
      simp only [sec7_symm_smul σ ν hν, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul,
        map_mul, RingEquiv.apply_symm_apply]
      ring)
    (fun x y y' => by simp only [map_add, mul_add])
    (fun c x y => by
      simp only [sec7_symm_smul σ ν hν, LinearMap.map_smul, smul_eq_mul, map_mul,
        RingEquiv.apply_symm_apply]
      ring)

theorem sec7_semilinear_proportional {K E : Type*} [Field K] [Finite K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (f : LinearMap.BilinForm K E) (hf : f.Nondegenerate) (hr : f.IsRefl)
    (U : Submodule K E) (hU : Module.finrank K U = 4) (ψ : E →ₗ[K] E)
    (hr1 : LinearMap.range ψ = U) (hk1 : LinearMap.ker ψ = f.orthogonal U)
    (σ : K ≃+* K) (ν : E ≃+ E) (hν : ∀ (c : K) (e : E), ν (c • e) = σ c • ν e)
    (a : K) (ha : a ≠ 0) (hνf : ∀ e e', f (ν e) (ν e') = a * σ (f e e'))
    (hνU : ∀ e, e ∈ U ↔ ν e ∈ U)
    (β₁ : LinearMap.BilinForm K U)
    (hβ₁ : ∀ (x y : U) (c : E), ψ c = (y : E) → β₁ x y = f x c) (h₁ : β₁.Nondegenerate)
    (O : Set (Submodule K U)) (hO1 : ∀ P ∈ O, Module.finrank K P = 1)
    (hcard : O.ncard = Nat.card K ^ 2 + 1)
    (hline : ∀ l : Submodule K U, Module.finrank K l = 2 → {P | P ∈ O ∧ P ≤ l}.ncard ≤ 2)
    (hplane : ∀ π : Submodule K U, Module.finrank K π = 3 →
      {P | P ∈ O ∧ P ≤ π}.ncard ≤ Nat.card K + 1)
    (hG : ∀ P ∈ O, ∀ x ∈ P, ∀ y x' y' : U, (x' : E) = ν x → (y' : E) = ν y →
      (β₁ x' y' = 0 ↔ β₁ x y = 0)) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ e : E, ψ e = μ • ν (ψ (ν.symm e)) := by
  obtain ⟨ψ', hψ'def, -⟩ := sec7_conj_semilinear_linear σ ν hν ψ
  obtain ⟨νU, hνUdef⟩ : ∃ νU : U ≃+ U, ∀ x : U, (νU x : E) = ν x :=
    ⟨sec7_restrictEquiv ν U hνU, fun x => rfl⟩
  have hνU' : ∀ (c : K) (v : U), νU (c • v) = σ c • νU v := by
    intro c v
    apply Subtype.ext
    simp [hνUdef, hν]
  obtain ⟨O₂, -, h2, h3, h4, h5, h6⟩ :=
    sec7_ovoid_map_semilinear σ νU hνU' O hO1 hcard hline hplane
  obtain ⟨β₂, hβ₂_apply⟩ : ∃ β₂ : LinearMap.BilinForm K U,
      ∀ x y : U, β₂ x y = a * σ (β₁ (νU.symm x) (νU.symm y)) :=
    ⟨sec7_transportForm σ νU hνU' a β₁, fun x y => rfl⟩
  have hid : ∀ n c : E, f (ν n) c = a * σ (f n (ν.symm c)) := by
    intro n c
    have h := hνf n (ν.symm c)
    rw [ν.apply_symm_apply] at h
    exact h
  have hβ₂ : ∀ (x y : U) (c : E), ψ' c = (y : E) → β₂ x y = f x c := by
    intro x y c hc
    obtain ⟨x₁, rfl⟩ := νU.surjective x
    obtain ⟨y₁, rfl⟩ := νU.surjective y
    have hy : ψ (ν.symm c) = (y₁ : E) := by
      apply ν.injective
      rw [← hψ'def c, hc, hνUdef y₁]
    have h := hβ₁ x₁ y₁ (ν.symm c) hy
    rw [hβ₂_apply, νU.symm_apply_apply, νU.symm_apply_apply, h, hνUdef x₁, hid]
  have h₂ : β₂.Nondegenerate := by
    constructor
    · intro x hx
      have hy : ∀ y₁ : U, β₁ (νU.symm x) y₁ = 0 := by
        intro y₁
        have h := hx (νU y₁)
        rw [hβ₂_apply, νU.symm_apply_apply] at h
        exact σ.map_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left ha)
      have hx0 : νU.symm x = 0 := h₁.1 (νU.symm x) hy
      calc x = νU (νU.symm x) := (νU.apply_symm_apply x).symm
        _ = 0 := by rw [hx0, map_zero]
    · intro y hy
      have hx : ∀ x₁ : U, β₁ x₁ (νU.symm y) = 0 := by
        intro x₁
        have h := hy (νU x₁)
        rw [hβ₂_apply, νU.symm_apply_apply] at h
        exact σ.map_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left ha)
      have hy0 : νU.symm y = 0 := h₁.2 (νU.symm y) hx
      calc y = νU (νU.symm y) := (νU.apply_symm_apply y).symm
        _ = 0 := by rw [hy0, map_zero]
  have hr2 : LinearMap.range ψ' = U := by
    ext e
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨e', rfl⟩
      rw [hψ'def e']
      apply (hνU _).mp
      rw [← hr1]
      exact LinearMap.mem_range_self ψ _
    · intro he
      have hs : ν.symm e ∈ U := (hνU (ν.symm e)).mpr (by rw [ν.apply_symm_apply]; exact he)
      rw [← hr1] at hs
      obtain ⟨e'', he''⟩ := LinearMap.mem_range.mp hs
      exact ⟨ν e'', by rw [hψ'def, ν.symm_apply_apply, he'', ν.apply_symm_apply]⟩
  have hortho : ∀ c : E, ν.symm c ∈ f.orthogonal U ↔ c ∈ f.orthogonal U := by
    intro c
    simp only [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h n hn
      have hns : ν.symm n ∈ U := (hνU (ν.symm n)).mpr (by rw [ν.apply_symm_apply]; exact hn)
      have h1 := h (ν.symm n) hns
      have h2' := hid (ν.symm n) c
      rw [ν.apply_symm_apply, h1, map_zero, mul_zero] at h2'
      exact h2'
    · intro h n hn
      have h1 := h (ν n) ((hνU n).mp hn)
      rw [hid] at h1
      exact σ.map_eq_zero_iff.mp ((mul_eq_zero.mp h1).resolve_left ha)
  have hk2 : LinearMap.ker ψ' = f.orthogonal U := by
    ext c
    rw [LinearMap.mem_ker, hψ'def c, ← hortho c, ← hk1, LinearMap.mem_ker]
    constructor
    · intro h
      apply ν.injective
      rw [h, map_zero]
    · intro h
      rw [h, map_zero]
  have hperp : ∀ P ∈ O₂, ∀ x ∈ P, ∀ y, β₂ x y = 0 ↔ β₁ x y = 0 := by
    intro P hP x hx y
    obtain ⟨P₁, hP₁, hPeq⟩ := h2 P hP
    have hx' : x ∈ νU '' (P₁ : Set U) := by
      rw [← hPeq]
      exact hx
    obtain ⟨x₁, hx₁, rfl⟩ := hx'
    obtain ⟨y₁, rfl⟩ := νU.surjective y
    have hG' := hG P₁ hP₁ x₁ hx₁ y₁ (νU x₁) (νU y₁) (hνUdef x₁) (hνUdef y₁)
    rw [hβ₂_apply, νU.symm_apply_apply, νU.symm_apply_apply, hG']
    constructor
    · intro h
      exact σ.map_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left ha)
    · intro h
      rw [h, map_zero, mul_zero]
  obtain ⟨μ, hμ0, hμ⟩ := sec7_maps_proportional_of_perp_agree f hf hr U hU ψ ψ' hr1 hr2 hk2
    β₁ β₂ hβ₁ hβ₂ h₁ h₂ O₂ h3 h4 h5 h6 hperp
  exact ⟨μ, hμ0, fun e => by rw [hμ e, hψ'def e]⟩

end CFSG.RankThree.GF2n.Stroth80
