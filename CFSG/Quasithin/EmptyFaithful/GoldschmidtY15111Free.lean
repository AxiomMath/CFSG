module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.Quasithin

namespace Y15111

variable {J : Type*} [Group J]

def conjEnd (W : Subgroup J) (c : J) (hc : c ∈ Subgroup.normalizer (W : Set J)) :
    Function.End ↥W := fun w => ⟨c * w * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc w).mp w.2⟩

theorem card_mod_three_of_free {W : Subgroup J} [Finite W] {c : J}
    (hc : c ∈ Subgroup.normalizer (W : Set J)) (hc3 : c ^ 3 = 1)
    (hfree : ∀ w ∈ W, c * w * c⁻¹ = w → w = 1) : Nat.card W % 3 = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype W := Fintype.ofFinite W
  have hc3' : c * c * c = 1 := by rw [← hc3, pow_succ, pow_succ, pow_one]
  let f : Function.End ↥W := conjEnd W c hc
  have hf : f ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    funext w
    apply Subtype.ext
    show c * (c * (c * (w : J) * c⁻¹) * c⁻¹) * c⁻¹ = w
    have : c * (c * (c * (w : J) * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * w * (c * c * c)⁻¹ := by
      group
    rw [this, hc3']
    simp
  have key := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have hfix : Nat.card (Function.fixedPoints f) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, ?_⟩⟩⟩
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      have ha' : c * (a : J) * c⁻¹ = a := congrArg Subtype.val ha
      have hb' : c * (b : J) * c⁻¹ = b := congrArg Subtype.val hb
      have h1 := hfree a a.2 ha'
      have h2 := hfree b b.2 hb'
      exact Subtype.ext (Subtype.ext (h1.trans h2.symm))
    · show f 1 = 1
      apply Subtype.ext
      show c * (1 : J) * c⁻¹ = 1
      simp
  have key' : Nat.card W ≡ Nat.card (Function.fixedPoints f) [MOD 3] := by
    convert key using 2
    · exact Nat.card_eq_fintype_card
    · rw [Nat.card_eq_fintype_card]
      congr
      funext a
      exact Subsingleton.elim _ _
  rw [hfix] at key'
  exact key'

end Y15111

end CFSG.Quasithin
