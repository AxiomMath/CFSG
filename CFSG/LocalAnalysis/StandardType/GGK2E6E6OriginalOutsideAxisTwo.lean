module

public import CFSG.LocalAnalysis.StandardType.GGK2E6E6OriginalSpanTwo
public import CFSG.LocalAnalysis.StandardType.GGK2E6E6Orbit

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6_dependent_orbit_card_ge_72_outside_axis
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {y : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hself : ∀ i, α i (h i) = 2)
    (hy : y ≠ 0) (hker : ∀ i, α i y = 0)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hdep : ¬ LinearIndependent (ZMod 3) h)
    {v : V} (hv : v ∉ Submodule.span (ZMod 3) {y}) :
    72 ≤ Nat.card (MulAction.orbit (E6QTwo.e6Weyl hself) v) := by
  classical
  obtain ⟨hS, _, hdec⟩ :=
    e6_dependent_span_card_and_axis_decomposition hpair hy hker hdim hdep
  obtain ⟨c, u, huS, heq⟩ := hdec v
  have hu : u ≠ 0 := by
    intro hu0
    apply hv
    rw [heq, hu0, add_zero]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton y))
  have hfix : ∀ g ∈ E6QTwo.e6Weyl hself, g y = y := by
    have hle : E6QTwo.e6Weyl hself ≤
        MulAction.stabilizer (V ≃ₗ[ZMod 3] V) y := by
      unfold E6QTwo.e6Weyl
      refine (Subgroup.closure_le (MulAction.stabilizer (V ≃ₗ[ZMod 3] V) y)).2 ?_
      rintro g ⟨i, rfl⟩
      apply MulAction.mem_stabilizer_iff.mpr
      change Module.reflection (hself i) y = y
      rw [Module.reflection_apply, hker i, zero_smul, sub_zero]
    intro g hg
    exact MulAction.mem_stabilizer_iff.mp (hle hg)
  rw [heq]
  exact e6_shifted_orbit_card_ge_72 hpair hself hS huS hu hfix c

theorem GGResHyp.K_E6_actual_orbit_ge_72
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (hyBs : y ∈ Bs)
    (φ : Fin 6 → MulAut ↥Bs) (h : Fin 6 → V) (α : Fin 6 → Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hlin : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i)
    (hgen : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hdep : ¬ LinearIndependent (ZMod 3) h)
    {v : V} (hv : v ∉ Submodule.span (ZMod 3)
      {ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))}) :
    72 ≤ Nat.card (MulAction.orbit
      ((ggAutomizer K Bs).map (ggLin (p := 3) ι)) v) := by
  classical
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hself : ∀ i, α i (h i) = 2 := by
    intro i
    rw [hpair]
    fin_cases i <;> decide
  have hmem : ∀ i, φ i ∈ ggAutomizer K Bs := by
    intro i
    rw [hgen]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hker := hH.K_simple_roots_kill_y ι hyBs φ h α hmem hself hlin
  have hy1 : y ≠ 1 := (hH.2.2.2.2.1.1 : LargeEvenSHat 3 B y K).2.2.1
  have hy0 : ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ≠ 0 := by
    intro hyzero
    have hyB1 : (⟨y, hyBs⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      apply ι.injective
      simpa using hyzero
    exact hy1 (congrArg Subtype.val hyB1)
  have hcardV : Nat.card V = 3 ^ 6 := by
    calc Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
      _ = Nat.card Bs := Nat.card_congr Additive.toMul
      _ = 3 ^ 6 := hcardBs
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at hc
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hc.symm
  rw [e6_actual_automizer_linear_map_eq ι φ h α hself hlin hgen]
  exact e6_dependent_orbit_card_ge_72_outside_axis hpair hself hy0 hker hdim hdep hv

end CFSG.StandardType

end
