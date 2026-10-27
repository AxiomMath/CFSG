module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixModuleAux

public section

namespace CFSG.StandardType

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6_span_orbit_card_ge_72
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2)
    (hS : Nat.card (E6QTwo.spanH h) = 3 ^ 5)
    {v : V} (hvS : v ∈ E6QTwo.spanH h) (hv : v ≠ 0) :
    72 ≤ Nat.card (MulAction.orbit (E6QTwo.e6Weyl hα) v) := by
  classical
  obtain ⟨B, hB⟩ := E6QTwo.exists_bilinForm_span hP hS
  let vS : E6QTwo.spanH h := ⟨v, hvS⟩
  have hvS0 : vS ≠ 0 := fun hz => hv (congrArg Subtype.val hz)
  let O := MulAction.orbit (E6QTwo.e6Weyl (E6QTwo.alphaIn_self hα)) vS
  have h72 : 72 ≤ Nat.card O := by
    rcases E6QTwo.orbit_cases (E6QTwo.alphaIn_hIn hP) hS hB
      (E6QTwo.alphaIn_self hα) hvS0 with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ <;>
      change 72 ≤ Nat.card (MulAction.orbit _ vS) <;> rw [hc] <;> norm_num
  let f : O → MulAction.orbit (E6QTwo.e6Weyl hα) v := fun s =>
    ⟨(s.val : V), by
      obtain ⟨g', hg'⟩ := MulAction.mem_orbit_iff.mp s.property
      obtain ⟨g, hg, hgeq⟩ := E6QTwo.lift_mem_e6Weyl (hα := hα) g'.property
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨⟨g, hg⟩, ?_⟩
      have heq := congrArg (fun z : E6QTwo.spanH h => (z : V)) hg'
      simpa only [Subgroup.smul_def, LinearEquiv.smul_def, hgeq vS] using heq⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hval := congrArg
      (fun s : MulAction.orbit (E6QTwo.e6Weyl hα) v => (s : V)) hab
    apply Subtype.ext
    apply Subtype.ext
    exact hval
  exact h72.trans (Nat.card_le_card_of_injective f hf)

theorem e6_shifted_orbit_card_ge_72
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2)
    (hS : Nat.card (E6QTwo.spanH h) = 3 ^ 5)
    {v y : V} (hvS : v ∈ E6QTwo.spanH h) (hv : v ≠ 0)
    (hy : ∀ g ∈ E6QTwo.e6Weyl hα, g y = y) (c : ZMod 3) :
    72 ≤ Nat.card (MulAction.orbit (E6QTwo.e6Weyl hα) (c • y + v)) := by
  classical
  let O := MulAction.orbit (E6QTwo.e6Weyl hα) v
  let f : O → MulAction.orbit (E6QTwo.e6Weyl hα) (c • y + v) := fun s =>
    ⟨c • y + s.val, by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp s.property
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨g, ?_⟩
      change (g.val : V ≃ₗ[ZMod 3] V) (c • y + v) = c • y + s.val
      rw [map_add, map_smul, hy g.val g.property]
      exact congrArg (fun w : V => c • y + w) hg⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val hab)
  exact (e6_span_orbit_card_ge_72 hP hα hS hvS hv).trans
    (Nat.card_le_card_of_injective f hf)

end CFSG.StandardType

end
