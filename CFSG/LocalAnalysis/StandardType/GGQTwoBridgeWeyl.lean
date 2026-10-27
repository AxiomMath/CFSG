module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private theorem ggQ2x_ggLin_simple {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (k : M.ι) :
    ggLin (p := p) M.model (M.simple k) = M.toLin.simpleRefl k := by
  refine LinearEquiv.ext fun v => ?_
  rw [M.simple_apply]
  exact (Module.reflection_apply v (M.toLin.root_coroot_self k)).symm

private theorem ggQ2x_image_eq {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (S : Set M.ι) :
    ggLin (p := p) M.model '' (M.simple '' S) = M.toLin.simpleRefl '' S := by
  ext t
  constructor
  · rintro ⟨φ, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, (ggQ2x_ggLin_simple M k).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨M.simple k, ⟨k, hk, rfl⟩, ggQ2x_ggLin_simple M k⟩

private theorem ggQ2x_parabL_unfold {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (S : Set M.ι) :
    M.parabL S = Subgroup.closure (M.toLin.simpleRefl '' S) := rfl

private theorem ggQ2x_parabL_eq {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (S : Set M.ι) :
    M.parabL S = (Subgroup.closure (M.simple '' S)).map (ggLin (p := p) M.model) := by
  rw [ggQ2x_parabL_unfold, MonoidHom.map_closure, ggQ2x_image_eq]
  rfl

private theorem ggQ2x_simple_mem_automizer_top {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (k : M.ι) : M.simple k ∈ ggAutomizer ⊤ Bs := by
  have hLK : M.simple k ∈ ggAutomizer L Bs ∨ M.simple k ∈ ggAutomizer K Bs := by
    by_cases hk : k ≠ M.a
    · left
      rw [M.automizer_L]
      exact Subgroup.subset_closure ⟨k, hk, rfl⟩
    · right
      rw [M.automizer_K]
      refine Subgroup.subset_closure ⟨k, ?_, rfl⟩
      intro hkb
      have hka : k = M.a := by simpa using hk
      exact M.a_ne_b (hka.symm.trans hkb)
  rcases hLK with h | h
  · exact ggAutomizer_mono Bs le_top h
  · exact ggAutomizer_mono Bs le_top h

private theorem ggQ2x_parabL_L {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) :
    M.parabL {k | k ≠ M.a} = (ggAutomizer L Bs).map (ggLin (p := p) M.model) := by
  rw [ggQ2x_parabL_eq, ← M.automizer_L]

private theorem ggQ2x_parabL_K {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) :
    M.parabL {k | k ≠ M.b} = (ggAutomizer K Bs).map (ggLin (p := p) M.model) := by
  rw [ggQ2x_parabL_eq, ← M.automizer_K]

private theorem ggQ2x_map_fix_iff {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (N : Subgroup (MulAut ↥Bs)) (v : M.V) :
    (∀ g ∈ N.map (ggLin (p := p) M.model), g v = v) ↔
      ∀ φ ∈ N, ggLin (p := p) M.model φ v = v := by
  constructor
  · intro h φ hφ
    exact h (ggLin (p := p) M.model φ) (Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩)
  · rintro h g hg
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
    exact h φ hφ

theorem ggQ2_weyl_le_lin {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G}
    (M : GGQTwoModel p Bs x y D L J K) :
    M.toLin.weyl ≤ M.linGroup := by
  have h : Subgroup.closure (M.toLin.simpleRefl '' Set.univ) ≤ M.linGroup :=
    (Subgroup.closure_le _).mpr fun t ht => by
      obtain ⟨k, -, rfl⟩ := ht
      exact Subgroup.mem_map.mpr ⟨M.simple k, ggQ2x_simple_mem_automizer_top M k,
        ggQ2x_ggLin_simple M k⟩
  exact h

theorem ggQ2_fixed_lin {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G}
    (M : GGQTwoModel p Bs x y D L J K) :
    (∀ v, (∀ g ∈ M.parabL {k | k ≠ M.a}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {M.xV}) ∧
    (∀ v, (∀ g ∈ M.parabL {k | k ≠ M.b}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {M.yV}) := by
  refine ⟨?_, ?_⟩
  · intro v
    rw [ggQ2x_parabL_L]
    rw [show Submodule.span (ZMod p) {M.xV} =
        ggFixedSubmodule (p := p) M.model (ggAutomizer L Bs) from M.fixed_x.symm]
    rw [mem_ggFixedSubmodule_iff]
    exact ggQ2x_map_fix_iff M (ggAutomizer L Bs) v
  · intro v
    rw [ggQ2x_parabL_K]
    rw [show Submodule.span (ZMod p) {M.yV} =
        ggFixedSubmodule (p := p) M.model (ggAutomizer K Bs) from M.fixed_y.symm]
    rw [mem_ggFixedSubmodule_iff]
    exact ggQ2x_map_fix_iff M (ggAutomizer K Bs) v

theorem ggQ2_card_L {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G}
    (M : GGQTwoModel p Bs x y D L J K) :
    Nat.card (ggAutomizer L Bs) = Nat.card (M.parabL {k | k ≠ M.a}) := by
  rw [ggQ2x_parabL_L]
  exact Nat.card_congr (Subgroup.equivMapOfInjective (ggAutomizer L Bs)
    (ggLin (p := p) M.model) (ggLin_injective M.model)).toEquiv

end CFSG.StandardType

end
