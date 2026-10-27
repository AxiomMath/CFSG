module

public import CFSG.Quasithin.Background.SzG11B49Shape
public import CFSG.Quasithin.Background.SzG11B49Tl

public section

namespace CFSG.Quasithin.G11.SzG11S

open Module CFSG.GroupTheory.GLnTwoSplitting

namespace B49Aux

theorem exists_two_ne_one {G : Type*} [Group G] (E : Subgroup G) (hE : Nat.card E = 4) :
    ∃ e₁ e₂ : G, e₁ ∈ E ∧ e₂ ∈ E ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite E
  have h2 : 2 < Fintype.card E := by
    rw [← Nat.card_eq_fintype_card, hE]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h2
  by_cases ha : (a : G) = 1
  · refine ⟨b, c, b.2, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro h
      exact hab (Subtype.ext (by rw [ha, h]))
    · intro h
      exact hac (Subtype.ext (by rw [ha, h]))
  · by_cases hb : (b : G) = 1
    · refine ⟨a, c, a.2, c.2, ha, ?_, fun h => hac (Subtype.ext h)⟩
      intro h
      exact hbc (Subtype.ext (by rw [hb, h]))
    · exact ⟨a, b, a.2, b.2, ha, hb, fun h => hab (Subtype.ext h)⟩

end B49Aux

open B49Aux

namespace B49Hyp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V} {H : Subgroup (GLV V)}
  {U : Submodule (ZMod 2) V} (hy : B49Hyp B H U)

include hy

theorem exists_isTv_of_act [Finite V] {e : GLV V} (he : e ∈ H) {a : V} (haU : a ∈ U)
    (ha0 : a ≠ 0) (hcen : ∀ u ∈ U, e u - u ∈ Submodule.span (ZMod 2) {a}) :
    ∃ v, B49Tv B H U e v a := by
  obtain ⟨x₀, hx₀⟩ := hy.exists_pair ha0
  have hx₀' : B x₀ a = 1 := by rw [hy.symm]; exact hx₀
  have hact : ∀ u ∈ U, ∃ c : ZMod 2, e u = u + c • a := fun u hu => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hcen u hu)
    rw [two_sub] at hc
    refine ⟨c, ?_⟩
    calc e u = e u + u + u := by rw [add_assoc, two_add_self, add_zero]
      _ = c • a + u := by rw [← hc]
      _ = u + c • a := add_comm _ _
  have hea : e a = a := by
    obtain ⟨c, hc⟩ := hact a haU
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · rw [hc, zero_smul, add_zero]
    · exfalso
      rw [one_smul, two_add_self] at hc
      exact ha0 (e.injective (by rw [hc, map_zero]))
  have hee : e * e = 1 := by
    refine hy.eq_one_of_eqOn (H.mul_mem he he) fun u hu => ?_
    obtain ⟨c, hc⟩ := hact u hu
    change e (e u) = u
    rw [hc, map_add, map_smul, hea, hc]
    match_scalars <;> ring_nf
    reduce_mod_char
  have hee' : ∀ x, e (e x) = x := fun x => by
    have := congrArg (fun g : GLV V => g x) hee
    simpa using this
  have hsa : ∀ x y, B (e x) y = B x (e y) := fun x y => by
    have := hy.isom e he x (e y)
    rwa [hee' y] at this
  have key : ∀ u ∈ U, B (e x₀ + x₀) u = B x₀ (e u + u) := fun u hu => by
    simp only [map_add, LinearMap.add_apply, hsa x₀ u]
  refine ⟨e x₀ + x₀, haU, ?_, he, fun u hu => ?_⟩
  · rw [key a haU, hea, two_add_self, map_zero]
  · obtain ⟨c, hc⟩ := hact u hu
    have h1 : e u + u = c • a := by
      rw [hc, add_comm, ← add_assoc, two_add_self, zero_add]
    have h2 : B (e x₀ + x₀) u = c := by
      rw [key u hu, h1, map_smul, hx₀', smul_eq_mul, mul_one]
    rw [h2]
    exact hc


theorem quadAt_of_E [Finite V] (E : Subgroup (GLV V)) (hEH : E ≤ H) (hE : Nat.card E = 4)
    {a : V} (haU : a ∈ U) (ha0 : a ≠ 0)
    (hcen : ∀ e ∈ E, ∀ u ∈ U, e u - u ∈ Submodule.span (ZMod 2) {a})
    (hquad : ∀ e ∈ E, ∀ e' ∈ E, ∀ v : V, e (e' v - v) = e' v - v) :
    ∀ z ∈ U, z ≠ 0 → B49Quad B H U z := by
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨e₁, e₂, he₁, he₂, h1, h2, h12⟩ := exists_two_ne_one E hE
  obtain ⟨v₁, hv₁⟩ := hy.exists_isTv_of_act (hEH he₁) haU ha0 (hcen e₁ he₁)
  obtain ⟨v₂, hv₂⟩ := hy.exists_isTv_of_act (hEH he₂) haU ha0 (hcen e₂ he₂)
  have hq12 : ∀ x, e₁ (e₂ x + x) = e₂ x + x := fun x => by
    have := hquad e₁ he₁ e₂ he₂ x
    rwa [two_sub] at this
  have n1 : ∃ u ∈ U, B v₁ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h1 (hy.tv_eq_one hv₁ hcon)
  have n2 : ∃ u ∈ U, B v₂ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h2 (hy.tv_eq_one hv₂ hcon)
  have n12 : ∃ u ∈ U, B v₁ u ≠ B v₂ u := by
    by_contra hcon
    push Not at hcon
    exact h12 (hy.tv_eq hv₁ hv₂ fun u hu => by rw [hcon u hu])
  intro z hz hz0 v v' t t' ht ht' x
  by_cases c1 : ∀ u ∈ U, B v u = 0
  · rw [hy.tv_eq_one ht c1]
    rfl
  by_cases c2 : ∀ u ∈ U, B v' u = 0
  · rw [hy.tv_eq_one ht' c2]
    change t (x + x) = x + x
    rw [two_add_self, map_zero]
  by_cases c3 : ∀ u ∈ U, B v u = B v' u
  · have : t = t' := hy.tv_eq ht ht' fun u hu => by rw [c3 u hu]
    subst this
    exact hy.tv_D_self ht x
  push Not at c1 c2 c3
  have hne : ∀ {w w' : V}, (∃ u ∈ U, B w u ≠ B w' u) →
      (B w).comp U.subtype ≠ (B w').comp U.subtype := by
    rintro w w' ⟨u, hu, hne⟩ h
    exact hne (by simpa using LinearMap.congr_fun h ⟨u, hu⟩)
  have hne0 : ∀ {w : V}, (∃ u ∈ U, B w u ≠ 0) → (B w).comp U.subtype ≠ 0 := by
    rintro w ⟨u, hu, hne⟩ h
    exact hne (by simpa using LinearMap.congr_fun h ⟨u, hu⟩)
  obtain ⟨γ, hγz, hγ1, hγ2⟩ := exists_equiv_triple (z := (⟨a, haU⟩ : U)) (z' := (⟨z, hz⟩ : U))
    (by simpa using ha0) (by simpa using hz0) (hne0 n1) (hne0 n2) (hne n12) (hne0 c1) (hne0 c2)
    (hne c3) (by simpa using hv₁.vz) (by simpa using hv₂.vz) (by simpa using ht.vz)
    (by simpa using ht'.vz)
  obtain ⟨k, hk, hk'⟩ := hy.aut γ
  have ka : k a = z := by
    have := hk' ⟨a, haU⟩
    rw [this, hγz]
  have hkcls : ∀ w w' : V, (B w').comp U.subtype ∘ₗ (γ : U →ₗ[ZMod 2] U) = (B w).comp U.subtype →
      ∀ u ∈ U, B (k w) u = B w' u := by
    intro w w' hγ u hu
    rw [hy.B_apply_left hk]
    have hmem : k⁻¹ u ∈ U := hy.inv_apply_mem hk hu
    have h1 : (γ ⟨k⁻¹ u, hmem⟩ : V) = u := by
      rw [← hk' ⟨k⁻¹ u, hmem⟩]
      exact apply_inv_apply k u
    have h2 := LinearMap.congr_fun hγ ⟨k⁻¹ u, hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, h1] at h2
    exact h2.symm
  have ht1 : B49Tv B H U (k * e₁ * k⁻¹) v z := by
    have := hy.tv_conj hv₁ hk
    rw [ka] at this
    exact this.congr (fun u hu => (hkcls v₁ v hγ1 u hu).symm) ht.vz
  have ht2 : B49Tv B H U (k * e₂ * k⁻¹) v' z := by
    have := hy.tv_conj hv₂ hk
    rw [ka] at this
    exact this.congr (fun u hu => (hkcls v₂ v' hγ2 u hu).symm) ht'.vz
  have htt : t = k * e₁ * k⁻¹ := hy.tv_eq ht ht1 fun u hu => rfl
  have htt' : t' = k * e₂ * k⁻¹ := hy.tv_eq ht' ht2 fun u hu => rfl
  subst htt htt'
  have hx : x = k (k⁻¹ x) := (apply_inv_apply k x).symm
  generalize k⁻¹ x = y at hx
  subst hx
  have e : (k * e₂ * k⁻¹) (k y) + k y = k (e₂ y + y) := by
    change k (e₂ (k⁻¹ (k y))) + k y = _
    rw [inv_apply_apply, map_add]
  rw [e]
  change k (e₁ (k⁻¹ (k (e₂ y + y)))) = k (e₂ y + y)
  rw [inv_apply_apply, hq12]

end B49Hyp

end CFSG.Quasithin.G11.SzG11S
