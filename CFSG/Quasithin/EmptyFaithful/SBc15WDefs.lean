module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc15

section Wreath

variable {D : Type} [Group D]

instance instFiniteRegularWreathProduct [Finite D] :
    Finite (D ≀ᵣ Multiplicative (ZMod 2)) :=
  Finite.of_injective (fun w : D ≀ᵣ Multiplicative (ZMod 2) => (w.left, w.right)) fun a b h => by
    ext
    · exact congrFun (congrArg Prod.fst h) _
    · exact congrArg Prod.snd h

@[expose] def wrPerf (D' : Subgroup D) : Subgroup (D ≀ᵣ Multiplicative (ZMod 2)) where
  carrier := {w | w.right = 1 ∧ ∀ i, w.left i ∈ D'}
  one_mem' := ⟨rfl, fun _ => D'.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by simp [ha, hb], fun i => ?_⟩
    simp only [RegularWreathProduct.mul_left, Pi.mul_apply]
    exact D'.mul_mem (ha' i) (hb' _)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨by simp [ha], fun i => ?_⟩
    simp only [RegularWreathProduct.inv_left, Pi.inv_apply]
    exact D'.inv_mem (ha' _)

end Wreath

@[expose] def WeakW (D : Type) [Group D] [Finite D] (D' : Subgroup D) : Prop :=
  (∀ T : Subgroup (D ≀ᵣ Multiplicative (ZMod 2)), IsSylowTwoOf T ⊤ →
      ∀ g, ∃ k ∈ wrPerf D', ∃ y ∈ T, g = k * y) ∧
    ∀ T X : Subgroup (D ≀ᵣ Multiplicative (ZMod 2)), IsSylowTwoOf T ⊤ → X ≤ wrPerf D' →
      T ≤ Subgroup.normalizer (X : Set (D ≀ᵣ Multiplicative (ZMod 2))) → oTwoUpper X = X →
        (∃ a : ℕ, Nat.card X = 9 * 2 ^ a) →
          ∀ k ∈ wrPerf D', (∀ w ∈ pCoreOf 2 (X ⊔ T ⊓ wrPerf D'), k * w * k⁻¹ ∈ T ⊓ wrPerf D') →
            k ∈ X ⊔ T ⊓ wrPerf D'

end SBc15

end CFSG.Quasithin
