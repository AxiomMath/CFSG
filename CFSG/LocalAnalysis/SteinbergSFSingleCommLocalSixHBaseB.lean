module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommParts

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Irreducible

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixH_conj_symm (φ : L ≃* antiSp K) (g y : antiSp K) :
    ((φ.symm g : L) : G) * ((φ.symm y : L) : G) * ((φ.symm g : L) : G)⁻¹ =
      ((φ.symm (g * y * g⁻¹) : L) : G) := by
  simp [map_mul, map_inv]

theorem sixH_i1_conj_coord (φ : L ≃* antiSp K) (k : Axis) {b b' : K} (hb : b ≠ 0)
    (hb' : b' ≠ 0) :
    ∃ j ∈ J₀ φ, j * RootAxisTwoCore.coordG φ k b * j⁻¹ = RootAxisTwoCore.coordG φ k b' := by
  cases k with
  | one =>
    obtain ⟨δ, hδ, hconj⟩ := exists_diagTorus_conj_axisOne hb hb'
    refine ⟨((φ.symm δ⁻¹ : L) : G), symm_mem_pull.2 (inv_mem hδ), ?_⟩
    have key := sixH_conj_symm φ δ⁻¹ (uElt 0 b 0 0)
    rw [inv_inv, hconj] at key
    exact key
  | two =>
    obtain ⟨δ, hδ, hconj⟩ :=
      exists_diagTorus_conj (b := 0) (b' := 0) hb hb' (Or.inl ⟨rfl, rfl⟩)
    refine ⟨((φ.symm δ⁻¹ : L) : G), symm_mem_pull.2 (inv_mem hδ), ?_⟩
    have key := sixH_conj_symm φ δ⁻¹ (uElt 0 0 b 0)
    rw [inv_inv, hconj] at key
    exact key

theorem sixH_i1_irreducible_U (k : Axis) {X : Subgroup G} (hXU : X ≤ U φ k)
    (hJ : ∀ j ∈ J₀ φ, ∀ x ∈ X, j * x * j⁻¹ ∈ X) : X = ⊥ ∨ X = U φ k := by
  by_cases hX : X = ⊥
  · exact Or.inl hX
  · right
    rw [Subgroup.eq_bot_iff_forall] at hX
    push Not at hX
    obtain ⟨x0, hx0X, hx0⟩ := hX
    obtain ⟨b0, rfl⟩ := RootAxisTwoCore.exists_coordG_eq φ k (hXU hx0X)
    have hb0 : b0 ≠ 0 := by
      rintro rfl
      exact hx0 (RootAxisTwoCore.coordG_zero φ k)
    apply le_antisymm hXU
    intro u hu
    obtain ⟨b, rfl⟩ := RootAxisTwoCore.exists_coordG_eq φ k hu
    by_cases hb : b = 0
    · subst hb
      rw [RootAxisTwoCore.coordG_zero φ k]
      exact X.one_mem
    · obtain ⟨j, hj, hjb⟩ := sixH_i1_conj_coord φ k hb0 hb
      have hmem := hJ j hj _ hx0X
      rw [hjb] at hmem
      exact hmem

open scoped Pointwise in
theorem sixH_i2_aux (h : FullCenter.FCHyp L K n φ t) (k : Axis) {X : Subgroup G}
    (hAX : A φ k ≤ X) (hXK : X ≤ Kc φ t k)
    (hJ : ∀ j ∈ J₀ φ, ∀ x ∈ X, j * x * j⁻¹ ∈ X) :
    X = A φ k ∨ X = Kc φ t k := by
  have hdec : ∀ x ∈ Kc φ t k,
      ∃ a ∈ A φ k, ∃ w ∈ Wk φ t k, ∃ u ∈ U φ k.swap, x = a * (w * u) := by
    intro x hx
    have hx' : x ∈ ((A φ k : Subgroup G) : Set G) * ((F φ t ⊓ D φ t k : Subgroup G) : Set G) := by
      rw [FullCenterWeyl.K_mul h k]
      exact hx
    obtain ⟨a, ha, f, hf, rfl⟩ := Set.mem_mul.1 hx'
    have hf' : f ∈ ((F φ t ⊓ D φ t k : Subgroup G) : Set G) := hf
    rw [← FullCenterTorus.W_mul_U h k] at hf'
    obtain ⟨w, hw, u, hu, rfl⟩ := Set.mem_mul.1 hf'
    exact ⟨a, ha, w, hw, u, hu, rfl⟩
  have hUkA : U φ k ≤ A φ k := pull_mono φ (FullCenter.rootU_le_rootA k)
  have hUsA : U φ k.swap ≤ A φ k :=
    pull_mono φ ((FullCenter.rootU_le_center (K := K) k.swap).trans
      (FullCenter.center_le_rootA (K := K) k))
  obtain ⟨hN, θ, -, hθ2⟩ := FullCenterTorus.quotient_W h k
  haveI := hN
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥(Wk φ t k) →* G, ∀ z : ↥(Wk φ t k),
      ψ z = ((θ (QuotientGroup.mk z) : ↥(U φ k)) : G) :=
    ⟨(U φ k).subtype.comp (θ.toMonoidHom.comp (QuotientGroup.mk' ((U φ k).subgroupOf (Wk φ t k)))),
      fun z => rfl⟩
  have hψU : ∀ z, ψ z ∈ U φ k := fun z => by
    rw [hψ z]
    exact (θ (QuotientGroup.mk z)).2
  have hker : ∀ z : ↥(Wk φ t k), ψ z = 1 → (z : G) ∈ U φ k := by
    intro z hz
    rw [hψ z] at hz
    have h1 : θ (QuotientGroup.mk z) = 1 := Subtype.ext hz
    have h2 := θ.injective (h1.trans (map_one θ).symm)
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff z).1 h2)
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup G,
      Y = (((Wk φ t k ⊓ X).subgroupOf (Wk φ t k)).map ψ) := ⟨_, rfl⟩
  have hYU : Y ≤ U φ k := by
    intro y hy
    rw [hYdef, Subgroup.mem_map] at hy
    obtain ⟨s, -, rfl⟩ := hy
    exact hψU s
  have hYJ : ∀ j ∈ J₀ φ, ∀ y ∈ Y, j * y * j⁻¹ ∈ Y := by
    intro j hj y hy
    rw [hYdef, Subgroup.mem_map] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hs
    obtain ⟨x', hx'1, hx'2⟩ := hθ2 j⁻¹ (inv_mem hj) s
    rw [inv_inv] at hx'1 hx'2
    rw [hYdef]
    refine Subgroup.mem_map.2 ⟨x', ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨x'.2, ?_⟩
      rw [hx'1]
      exact hJ j hj _ hs.2
    · rw [hψ x', hψ s]
      exact hx'2
  rcases sixH_i1_irreducible_U k hYU hYJ with hY | hY
  · left
    refine le_antisymm ?_ hAX
    intro x hx
    obtain ⟨a, ha, w, hw, u, hu, rfl⟩ := hdec x (hXK hx)
    have hwu : w * u ∈ X := by
      have := X.mul_mem (X.inv_mem (hAX ha)) hx
      simpa using this
    have hwX : w ∈ X := by
      have := X.mul_mem hwu (X.inv_mem (hAX (hUsA hu)))
      simpa using this
    have hψw : ψ ⟨w, hw⟩ ∈ Y := by
      rw [hYdef]
      exact Subgroup.mem_map.2
        ⟨⟨w, hw⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hw, hwX⟩), rfl⟩
    rw [hY, Subgroup.mem_bot] at hψw
    have hwU : w ∈ U φ k := hker ⟨w, hw⟩ hψw
    exact Subgroup.mul_mem _ ha (Subgroup.mul_mem _ (hUkA hwU) (hUsA hu))
  · right
    have hWX : Wk φ t k ≤ X := by
      intro w hw
      have hψw : ψ ⟨w, hw⟩ ∈ Y := by
        rw [hY]
        exact hψU ⟨w, hw⟩
      rw [hYdef, Subgroup.mem_map] at hψw
      obtain ⟨s, hs, hsw⟩ := hψw
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hs
      have hsu : ψ (s⁻¹ * ⟨w, hw⟩) = 1 := by
        rw [map_mul, map_inv, hsw, inv_mul_cancel]
      have hmem := hker _ hsu
      have key : (s : G) * ((s⁻¹ * ⟨w, hw⟩ : ↥(Wk φ t k)) : G) ∈ X :=
        X.mul_mem hs.2 (hAX (hUkA hmem))
      simpa using key
    apply le_antisymm hXK
    intro x hx
    obtain ⟨a, ha, w, hw, u, hu, rfl⟩ := hdec x hx
    exact X.mul_mem (hAX ha) (X.mul_mem (hWX hw) (hAX (hUsA hu)))

theorem sixH_i2_irreducible_K (hS : SCSetting L K n φ t i) {X : Subgroup G}
    (hAX : A φ i.swap ≤ X) (hXK : X ≤ Kc φ t i.swap)
    (hJ : ∀ j ∈ J₀ φ, ∀ x ∈ X, j * x * j⁻¹ ∈ X) :
    X = A φ i.swap ∨ X = Kc φ t i.swap := by
  exact sixH_i2_aux hS.fc i.swap hAX hXK hJ

end Irreducible

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
