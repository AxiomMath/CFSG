module

public import CFSG.Quasithin.EmptyFaithful.S152NWreath
public import CFSG.Quasithin.EmptyFaithful.S152He8Lin

public section

namespace CFSG.Quasithin.He8

open CFSG.Quasithin.S152N Matrix

namespace WCoord

noncomputable local instance instFintypeW : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEqW : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance instDecN0 : DecidablePred (· ∈ W3.N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

@[expose] def c3 : Equiv.Perm (Fin 3) := finRotate 3

@[expose] def fW (v : Fin 2 → ZMod 3) : W3 :=
  ⟨fun q => c3 ^ (v (if q = 1 then 0 else 1)).val, 1⟩

theorem fW_add : ∀ v w : Fin 2 → ZMod 3, fW (v + w) = fW v * fW w := by decide +kernel

theorem fW_mem : ∀ v : Fin 2 → ZMod 3, fW v ∈ W3.N0 := by decide +kernel

theorem fW_injective : ∀ v w : Fin 2 → ZMod 3, fW v = fW w → v = w := by decide +kernel

theorem fW_surjective : ∀ x : W3, x ∈ W3.N0 → ∃ v : Fin 2 → ZMod 3, fW v = x := by decide +kernel

theorem exists_mon_of_conj : ∀ w : W3, ∃ M : Matrix (Fin 2) (Fin 2) (ZMod 3), IsMon M ∧
    ∀ v : Fin 2 → ZMod 3, w * fW v * w⁻¹ = fW (M *ᵥ v) := by decide +kernel

theorem exists_conj_of_mon : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3), IsMon M →
    ∃ w : W3, ∀ v : Fin 2 → ZMod 3, w * fW v * w⁻¹ = fW (M *ᵥ v) := by decide +kernel

end WCoord

end CFSG.Quasithin.He8
