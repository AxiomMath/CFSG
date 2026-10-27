module

public import CFSG.RankThree.PartOne.N1322.Bridge1

public section

namespace CFSG.RankThree.PartOne.N1322

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G} {c : G}
  {L E : Subgroup G} (f : Multiplicative (Fin 3 → ZMod p) ≃* E)

theorem X_irreducible (h12 : Sec12Hyp G p A c L E) (hF12 : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) {v : Fin 3 → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) (hv0 : v ≠ 0) :
    ∀ U : Submodule (ZMod p) (Fin 3 → ZMod p),
      (∀ g ∈ (reflectionGroup p E).map (LinAlg.coordGL f), ∀ w ∈ U,
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hU0, hU1⟩ := hne
  have hUX : ∀ φ ∈ reflectionGroup p E, ∀ x ∈ U, LinAlg.coordHom f φ x ∈ U := by
    intro φ hφ x hx
    have := hU (LinAlg.coordGL f φ) (Subgroup.mem_map_of_mem _ hφ) x hx
    rwa [coordGL_mulVec_eq] at this
  have hLle := torusImage_le_reflectionGroup hF12
  have hUL : ∀ l ∈ (torusImage E L).map (LinAlg.coordHom f), ∀ x ∈ U, l x ∈ U := by
    intro l hl x hx
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hl
    exact hUX ψ (hLle hψ) x hx
  have hcases := inv_cases f h12 hF12 hv hv0 U hUL hU0 hU1
  have hfrv : Module.finrank (ZMod p) (Submodule.span (ZMod p) {v}) = 1 :=
    finrank_span_singleton hv0
  have hfinU : Module.finrank (ZMod p) U = 1 ∨ Module.finrank (ZMod p) U = 2 := by
    rcases hcases with h | ⟨-, h⟩
    · left; rw [h, hfrv]
    · right; omega
  have hW : ∀ φ ∈ torusWeyl E, ∀ x ∈ U, LinAlg.coordHom f φ x ∈ U := by
    intro φ hφ
    have hfin : Module.finrank (ZMod p) (U.map (LinAlg.coordHom f φ).toLinearMap) =
        Module.finrank (ZMod p) U := LinearEquiv.finrank_map_eq _ U
    have hU'0 : U.map (LinAlg.coordHom f φ).toLinearMap ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hfin
      omega
    have hU'1 : U.map (LinAlg.coordHom f φ).toLinearMap ≠ ⊤ := by
      intro h
      rw [h, finrank_top, Module.finrank_fin_fun] at hfin
      omega
    have hU'inv : ∀ l ∈ (torusImage E L).map (LinAlg.coordHom f),
        ∀ x ∈ U.map (LinAlg.coordHom f φ).toLinearMap,
          l x ∈ U.map (LinAlg.coordHom f φ).toLinearMap := by
      intro l hl x hx
      obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hl
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have hmem : φ⁻¹ * ψ * φ ∈ reflectionGroup p E := by
        have := Sec1322.conj_mem_reflectionGroup (Fact.out : p.Prime) ((torusWeyl E).inv_mem hφ)
          (hLle hψ)
        simpa using this
      refine Submodule.mem_map.mpr ⟨LinAlg.coordHom f (φ⁻¹ * ψ * φ) y, hUX _ hmem y hy, ?_⟩
      simp
    have hcases' := inv_cases f h12 hF12 hv hv0 _ hU'inv hU'0 hU'1
    have hUeq : U.map (LinAlg.coordHom f φ).toLinearMap = U := by
      rcases hcases with hc | ⟨hc, hc2⟩ <;> rcases hcases' with hc' | ⟨hc', hc2'⟩
      · rw [hc', hc]
      · exfalso
        have hfU : Module.finrank (ZMod p) U = 1 := by rw [hc, hfrv]
        omega
      · exfalso
        have hfU' : Module.finrank (ZMod p) (U.map (LinAlg.coordHom f φ).toLinearMap) = 1 := by
          rw [hc', hfrv]
        omega
      · rw [hc', hc]
    intro x hx
    have : LinAlg.coordHom f φ x ∈ U.map (LinAlg.coordHom f φ).toLinearMap :=
      Submodule.mem_map_of_mem hx
    rwa [hUeq] at this
  rcases Sec127.irreducible_map f hF13.irreducible U (fun g hg x hx => by
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
      exact hW φ hφ x hx) with h | h
  · exact hU0 h
  · exact hU1 h

omit [Finite G] in
theorem row_cases {Γ : Subgroup (MulAut E)} {r : ℕ} (h2 : 2 ≤ r) (h8 : r ≤ 8)
    (hw : RowWeylIso E Γ r) :
    (Nonempty (Γ ≃* DihedralGroup 6) ∧ (r = 2 ∨ r = 3)) ∨
      (Nonempty (Γ ≃* DihedralGroup 8) ∧ r = 4) ∨
      (Nonempty (Γ ≃* DihedralGroup 4) ∧ (r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8)) := by
  interval_cases r
  · exact Or.inl ⟨hw, Or.inl rfl⟩
  · exact Or.inl ⟨hw, Or.inr rfl⟩
  · exact Or.inr (Or.inl ⟨hw, rfl⟩)
  · exact Or.inr (Or.inr ⟨hw, Or.inl rfl⟩)
  · exact Or.inr (Or.inr ⟨hw, Or.inr (Or.inl rfl)⟩)
  · exact Or.inr (Or.inr ⟨hw, Or.inr (Or.inr (Or.inl rfl))⟩)
  · exact Or.inr (Or.inr ⟨hw, Or.inr (Or.inr (Or.inr rfl))⟩)

end CFSG.RankThree.PartOne.N1322
