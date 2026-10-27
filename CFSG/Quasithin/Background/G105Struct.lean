module

public import CFSG.Quasithin.Background.G105Lin
public import CFSG.Quasithin.Background.G10Basic

public section

namespace CFSG.Quasithin.G105

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem not_mem_of_invariant {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)}
    {v₁ : V} {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}
    (hG : G101Hyp B Γ v₁ W X X₀) {P : Submodule (ZMod 2) V} (hP : Invariant Γ P)
    (hPne : P ≠ ⊤) : v₁ ∉ P := by
  intro hv
  apply hPne
  rw [eq_top_iff, ← hG.span_orbit]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, rfl⟩
  exact hP γ γ.2 v₁ hv

theorem finrank_le_index [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)}
    {v₁ : V} {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}
    (hG : G101Hyp B Γ v₁ W X X₀) :
    Module.finrank (ZMod 2) V ≤ (MulAction.stabilizer Γ v₁).index := by
  classical
  haveI : Fintype (MulAction.orbit Γ v₁) := Fintype.ofFinite _
  have h1 := finrank_span_le_card (R := ZMod 2) (MulAction.orbit Γ v₁)
  rw [hG.span_orbit, finrank_top, ← Set.ncard_eq_toFinset_card'] at h1
  rw [MulAction.index_stabilizer]
  exact h1

theorem eq_one_of_sq_normal {Γ : Subgroup (GLV V)} (hO2 : pCoreOf 2 Γ = ⊥)
    {N : Subgroup (GLV V)} (hN : N ≤ Γ)
    (hNn : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (hsq : ∀ n ∈ N, n * n = 1) :
    ∀ n ∈ N, n = 1 := by
  set N' : Subgroup Γ := N.subgroupOf Γ with hN'
  have hnorm : N'.Normal := by
    constructor
    intro n hn g
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    have := hNn g g.2 n hn
    simpa using this
  have hpg : IsPGroup 2 N' := by
    intro g
    refine ⟨1, ?_⟩
    have hg : (g : GLV V) ∈ N := (Subgroup.mem_subgroupOf).1 g.2
    apply Subtype.ext
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one, OneMemClass.coe_one]
    rw [pow_two]
    exact hsq _ hg
  have hle : N' ≤ CFSG.pCore 2 Γ := le_sSup ⟨hnorm, hpg⟩
  intro n hn
  have hnΓ : n ∈ Γ := hN hn
  have hmem : (⟨n, hnΓ⟩ : Γ) ∈ N' := by
    rw [hN', Subgroup.mem_subgroupOf]
    exact hn
  have h4 : n ∈ pCoreOf 2 Γ := Subgroup.mem_map_of_mem Γ.subtype (hle hmem)
  rw [hO2, Subgroup.mem_bot] at h4
  exact h4

theorem isCompl_orthogonal_of_inf {B : LinearMap.BilinForm (ZMod 2) V}
    {Γ : Subgroup (GLV V)} {v₁ : V} {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}
    (hG : G101Hyp B Γ v₁ W X X₀) {U : Submodule (ZMod 2) V}
    (hU : U ⊓ B.orthogonal U = ⊥) : IsCompl U (B.orthogonal U) := by
  have hrefl : B.IsRefl := hG.isRefl
  refine LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl ?_
  have h1 : ∀ x : U, (∀ y : U, (B.restrict U) x y = 0) → x = 0 := by
    intro x hx
    have hx' : (x : V) ∈ B.orthogonal U := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      exact hrefl _ _ (hx ⟨n, hn⟩)
    have hmem : (x : V) ∈ U ⊓ B.orthogonal U := ⟨x.2, hx'⟩
    rw [hU, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  refine ⟨fun x hx => h1 x hx, fun x hx => h1 x fun y => ?_⟩
  exact hrefl _ _ (hx y)

theorem inducesTransvection_of_split [Finite V] {U U' : Submodule (ZMod 2) V}
    (hc : IsCompl U U') (hU2 : Module.finrank (ZMod 2) U = 2) {g : GLV V}
    (hgU' : ∀ w ∈ U', g w = w) {h : U ≃ₗ[ZMod 2] U} (hgh : ∀ u : U, g (u : V) = (h u : V))
    (hh2 : h * h = 1) (hh1 : h ≠ 1) : ∃ c : V, InducesTransvection g ⊤ c := by
  obtain ⟨c, hc1, u₀, hu₀⟩ := exists_transvection_of_involution U hU2 hh2 hh1
  refine ⟨c, fun v _ => ?_, ⟨(u₀ : V), Submodule.mem_top, ?_⟩⟩
  · have hv : v ∈ U ⊔ U' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    have hgw : g (u + w) - (u + w) = (g u : V) - (u : V) := by
      rw [map_add, hgU' w hw]
      abel
    rw [hgw, hgh ⟨u, hu⟩]
    exact hc1 ⟨u, hu⟩
  · rw [hgh u₀]
    intro h'
    apply hu₀
    exact Subtype.ext h'

end CFSG.Quasithin.G105
