module

public import CFSG.Quasithin.Background.SzG11B49Tv
public import CFSG.Quasithin.Background.SzG11B49Dim

public section

namespace CFSG.Quasithin.G11.SzG11S

open Module CFSG.GroupTheory.GLnTwoSplitting
open B49Aux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def B49Quad (B : LinearMap.BilinForm (ZMod 2) V) (H : Subgroup (GLV V))
    (U : Submodule (ZMod 2) V) (z : V) : Prop :=
  ∀ v v' t t', B49Tv B H U t v z → B49Tv B H U t' v' z → ∀ x, t (t' x + x) = t' x + x

namespace B49Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {H : Subgroup (GLV V)}
  {U : Submodule (ZMod 2) V} (hy : B49Hyp B H U) {t t' : GLV V} {v v' z : V}

include hy

theorem tv_D_span [Finite V] (hz0 : z ≠ 0) (hQ : B49Quad B H U z) (ht : B49Tv B H U t v z)
    {x : V} (hx : B z x = 0) : t x + x ∈ Submodule.span (ZMod 2) {z} := by
  have hxz : B x z = 0 := by rw [hy.symm]; exact hx
  have hU : t x + x ∈ U := by
    have := hy.tv_D_cls ht x
    rwa [hxz, zero_smul, add_zero] at this
  refine hy.mem_span_single_of_orth fun w hw => ?_
  have hwz : B w z = 0 := by rw [hy.symm]; exact hw
  obtain ⟨t', ht'⟩ := hy.exists_isTv ht.z_mem hwz
  have h1 := hQ w v t' t ht' ht x
  rw [ht'.act _ hU] at h1
  have h2 : B w (t x + x) • z = 0 := by simpa using h1
  rcases smul_eq_zero.1 h2 with h3 | h3
  · rw [hy.symm]; exact h3
  · exact absurd h3 hz0

theorem tv_shape [Finite V] (hz0 : z ≠ 0) (hQ : B49Quad B H U z) (ht : B49Tv B H U t v z) :
    ∃ a : V, (∀ u ∈ U, B a u = B v u) ∧ ∃ c : ZMod 2, ∀ x : V,
      t x + x = B a x • z + B z x • a + (c * B z x) • z := by
  obtain ⟨x₀, hx₀⟩ := hy.exists_pair hz0
  have hx₀' : B x₀ z = 1 := by rw [hy.symm]; exact hx₀
  refine ⟨t x₀ + x₀, ?_, B (t x₀ + x₀) x₀, fun x => ?_⟩
  · intro u hu
    have h1 := hy.tv_D_cls ht x₀
    rw [hx₀', one_smul] at h1
    have h2 := hy.iso _ h1 u hu
    simp only [map_add, LinearMap.add_apply] at h2 ⊢
    generalize B (t x₀) u = a at *
    generalize B x₀ u = b at *
    generalize B v u = c at *
    revert a b c
    decide
  · have hw : B z (x + B z x • x₀) = 0 := by
      rw [map_add, map_smul, smul_eq_mul, hx₀]
      generalize B z x = a
      revert a
      decide
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 (hy.tv_D_span hz0 hQ ht hw)
    rw [map_add, map_smul] at hc'
    have hD : t x + x = c' • z + B z x • (t x₀ + x₀) := by
      rw [hc']
      match_scalars <;> ring_nf <;> reduce_mod_char
    have hsa := hy.tv_selfadj ht x x₀
    rw [hD] at hsa
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hx₀] at hsa
    rw [hy.symm x (t x₀), hy.symm x x₀] at hsa
    have hc : c' = B (t x₀ + x₀) x + B (t x₀ + x₀) x₀ * B z x := by
      have hcs : ∀ a₁ a₂ a₃ a₄ a₅ c : ZMod 2,
          c * 1 + a₅ * (a₃ + a₄) = a₁ + a₂ → c = a₁ + a₂ + (a₃ + a₄) * a₅ := by decide
      simp only [map_add, LinearMap.add_apply]
      exact hcs _ _ _ _ _ _ hsa
    rw [hD, hc]
    match_scalars <;> ring_nf

end B49Hyp

@[expose] def B49Lam (B : LinearMap.BilinForm (ZMod 2) V) (t : GLV V) (z : V) (c : ZMod 2) :
    Prop :=
  ∀ x, B (t x + x) x = c * B z x

namespace B49Lam

variable {B : LinearMap.BilinForm (ZMod 2) V} {t t' : GLV V} {z a : V} {c c' : ZMod 2}

theorem of_shape (h : ∀ x : V, t x + x = B a x • z + B z x • a + (c * B z x) • z) :
    B49Lam B t z c := by
  intro x
  rw [h x]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hs : ∀ a₁ a₂ c : ZMod 2, a₁ * a₂ + a₂ * a₁ + c * a₂ * a₂ = c * a₂ := by decide
  exact hs _ _ _

theorem mul (hq : ∀ x, t (t' x + x) = t' x + x) (h : B49Lam B t z c) (h' : B49Lam B t' z c') :
    B49Lam B (t * t') z (c + c') := by
  intro x
  have e : (t * t') x + x = (t x + x) + (t' x + x) := by
    have h1 := hq x
    rw [map_add] at h1
    have h2 : t (t' x) = t' x + x + t x := by
      rw [← h1, add_assoc, two_add_self, add_zero]
    change t (t' x) + x = _
    rw [h2]
    abel
  rw [e, map_add, LinearMap.add_apply, h x, h' x, add_mul]

end B49Lam

namespace B49Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {H : Subgroup (GLV V)}
  {U : Submodule (ZMod 2) V} (hy : B49Hyp B H U) {t t' : GLV V} {v v' z : V} {c c' : ZMod 2}

include hy

theorem lam_unique (hz0 : z ≠ 0) (h : B49Lam B t z c) (h' : B49Lam B t z c') : c = c' := by
  obtain ⟨x₀, hx₀⟩ := hy.exists_pair hz0
  have h1 := h x₀
  have h2 := h' x₀
  rw [hx₀, mul_one] at h1 h2
  rw [← h1, ← h2]

theorem lam_conj (h : B49Lam B t z c) {g : GLV V} (hg : g ∈ H) (hgz : g z = z) :
    B49Lam B (g * t * g⁻¹) z c := by
  intro x
  have hx : x = g (g⁻¹ x) := (apply_inv_apply g x).symm
  generalize g⁻¹ x = y at hx
  subst hx
  have e : (g * t * g⁻¹) (g y) + g y = g (t y + y) := by
    change g (t (g⁻¹ (g y))) + g y = _
    rw [inv_apply_apply, map_add]
  rw [e, hy.isom g hg, h y]
  rw [← hy.isom g hg z y, hgz]


theorem exists_conj_cls [Finite V] (hz : z ∈ U) (hv : ∃ u ∈ U, B v u ≠ 0)
    (hv' : ∃ u ∈ U, B v' u ≠ 0) (hvz : B v z = 0) (hv'z : B v' z = 0) :
    ∃ g ∈ H, g z = z ∧ ∀ u ∈ U, B (g v) u = B v' u := by
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hφ : (B v').comp U.subtype ≠ 0 := by
    intro h
    obtain ⟨u, hu, hne⟩ := hv'
    exact hne (by simpa using LinearMap.congr_fun h ⟨u, hu⟩)
  have hψ : (B v).comp U.subtype ≠ 0 := by
    intro h
    obtain ⟨u, hu, hne⟩ := hv
    exact hne (by simpa using LinearMap.congr_fun h ⟨u, hu⟩)
  obtain ⟨γ, hγz, hγ⟩ := exists_comp_eq_of_apply_eq_zero (e₀ := (⟨z, hz⟩ : U)) hφ hψ
    (by simpa using hv'z) (by simpa using hvz)
  obtain ⟨k, hk, hk'⟩ := hy.aut γ
  refine ⟨k, hk, ?_, fun u hu => ?_⟩
  · rw [hk' ⟨z, hz⟩, hγz]
  · rw [hy.B_apply_left hk]
    have hmem : k⁻¹ u ∈ U := hy.inv_apply_mem hk hu
    have h1 : (γ ⟨k⁻¹ u, hmem⟩ : V) = u := by
      rw [← hk' ⟨k⁻¹ u, hmem⟩]
      exact apply_inv_apply k u
    have h2 := LinearMap.congr_fun hγ ⟨k⁻¹ u, hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, h1] at h2
    exact h2.symm

theorem exists_lam [Finite V] (hz0 : z ≠ 0) (hQ : B49Quad B H U z) (ht : B49Tv B H U t v z) :
    ∃ c, B49Lam B t z c := by
  obtain ⟨a, -, c, hc⟩ := hy.tv_shape hz0 hQ ht
  exact ⟨c, B49Lam.of_shape hc⟩

theorem lam_zero [Finite V] (hz0 : z ≠ 0) (hQ : B49Quad B H U z) (ht : B49Tv B H U t v z) :
    B49Lam B t z 0 := by
  have hz := ht.z_mem
  by_cases hcls : ∀ u ∈ U, B v u = 0
  · rw [hy.tv_eq_one ht hcls]
    intro x
    change B (x + x) x = 0 * B z x
    rw [two_add_self, zero_mul]
    simp
  · push Not at hcls
    obtain ⟨v₁, v₂, hv₁z, hv₂z, w₁, hw₁, w₂, hw₂, h11, h12, h21, h22⟩ :=
      hy.exists_two_forms hz0
    obtain ⟨t₁, ht₁⟩ := hy.exists_isTv hz hv₁z
    obtain ⟨t₂, ht₂⟩ := hy.exists_isTv hz hv₂z
    obtain ⟨c₁, hc₁⟩ := hy.exists_lam hz0 hQ ht₁
    obtain ⟨c₂, hc₂⟩ := hy.exists_lam hz0 hQ ht₂
    have n1 : ∃ u ∈ U, B v₁ u ≠ 0 := ⟨w₁, hw₁, by rw [h11]; exact one_ne_zero⟩
    have n2 : ∃ u ∈ U, B v₂ u ≠ 0 := ⟨w₂, hw₂, by rw [h22]; exact one_ne_zero⟩
    have key : ∀ (t' : GLV V) (v' : V), B49Tv B H U t' v' z → (∃ u ∈ U, B v' u ≠ 0) →
        B49Lam B t' z c₁ := by
      intro t' v' ht' hne
      obtain ⟨g, hg, hgz, hgcls⟩ := hy.exists_conj_cls hz n1 hne hv₁z ht'.vz
      have hconj : B49Tv B H U (g * t₁ * g⁻¹) v' z := by
        have := hy.tv_conj ht₁ hg
        rw [hgz] at this
        exact this.congr (fun u hu => (hgcls u hu).symm) ht'.vz
      have : t' = g * t₁ * g⁻¹ := hy.tv_eq ht' hconj fun u hu => rfl
      rw [this]
      exact hy.lam_conj hc₁ hg hgz
    have hc₂' : B49Lam B t₂ z c₁ := key t₂ v₂ ht₂ n2
    have e12 : c₂ = c₁ := hy.lam_unique hz0 hc₂ hc₂'
    have ht₃ : B49Tv B H U (t₁ * t₂) (v₁ + v₂) z := B49Tv.mul_axis ht₁ ht₂
    have n3 : ∃ u ∈ U, B (v₁ + v₂) u ≠ 0 :=
      ⟨w₁, hw₁, by simp only [map_add, LinearMap.add_apply, h11, h21]; simp⟩
    have hc₃ : B49Lam B (t₁ * t₂) z (c₁ + c₂) :=
      B49Lam.mul (hQ v₁ v₂ t₁ t₂ ht₁ ht₂) hc₁ hc₂
    have hc₃' : B49Lam B (t₁ * t₂) z c₁ := key _ _ ht₃ n3
    have e3 : c₁ + c₂ = c₁ := hy.lam_unique hz0 hc₃ hc₃'
    have hc₂0 : c₂ = 0 := add_eq_left.1 e3
    have hc₁0 : c₁ = 0 := by rw [← e12]; exact hc₂0
    have := key t v ht hcls
    rwa [hc₁0] at this

theorem tv_shape0 [Finite V] (hz0 : z ≠ 0) (hQ : B49Quad B H U z) (ht : B49Tv B H U t v z) :
    ∃ a : V, (∀ u ∈ U, B a u = B v u) ∧ ∀ x : V, t x + x = B a x • z + B z x • a := by
  obtain ⟨a, ha, c, hc⟩ := hy.tv_shape hz0 hQ ht
  have h1 : B49Lam B t z c := B49Lam.of_shape hc
  have h2 := hy.lam_zero hz0 hQ ht
  have hc0 : c = 0 := hy.lam_unique hz0 h1 h2
  subst hc0
  exact ⟨a, ha, fun x => by rw [hc x]; simp⟩

end B49Hyp

end CFSG.Quasithin.G11.SzG11S
