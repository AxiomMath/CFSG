module

public import CFSG.Quasithin.Background.RonanH143Data

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def vecOf (t : Fin 16) : Fin 2 → F4 :=
  ![⟨((t : ℕ) % 2 : ℕ), ((t : ℕ) / 2 % 2 : ℕ)⟩, ⟨((t : ℕ) / 4 % 2 : ℕ), ((t : ℕ) / 8 % 2 : ℕ)⟩]

theorem vecOf_xorF : ∀ s t : Fin 16, vecOf (xorF s t) = vecOf s + vecOf t := by
  decide +kernel

theorem vecOf_zero : vecOf 0 = 0 := by
  decide +kernel

theorem vecOf_injective : Function.Injective vecOf := by
  have key : ∀ s t : Fin 16, vecOf s = vecOf t → s = t := by decide +kernel
  exact fun s t h => key s t h

theorem vecOf_surjective : Function.Surjective vecOf := by
  intro v
  have key : ∀ a b c d : ZMod 2, ∃ t : Fin 16,
      vecOf t = (![⟨a, b⟩, ⟨c, d⟩] : Fin 2 → F4) := by
    decide +kernel
  obtain ⟨t, ht⟩ := key (v 0).re (v 0).im (v 1).re (v 1).im
  refine ⟨t, ?_⟩
  rw [ht]
  funext i
  fin_cases i <;> rfl

theorem exists_phiNQ : ∃ φ : ↥NQ ≃* Multiplicative (Fin 2 → F4),
    ∀ t : Fin 16, φ ⟨nqPerm t, ⟨t, rfl⟩⟩ = Multiplicative.ofAdd (vecOf t) := by
  choose idx hidx using fun x : ↥NQ => mem_NQ_iff.1 x.2
  have hinj : ∀ x y : ↥NQ, idx x = idx y → x = y := by
    intro x y h
    apply Subtype.ext
    rw [hidx x, hidx y, h]
  have hmul : ∀ x y : ↥NQ, idx (x * y) = xorF (idx x) (idx y) := by
    intro x y
    apply nqPerm_injective
    rw [← hidx (x * y), Subgroup.coe_mul, hidx x, hidx y, nqPerm_mul]
  have hone : idx 1 = 0 := by
    apply nqPerm_injective
    rw [← hidx 1, Subgroup.coe_one, nqPerm_zero]
  have hself : ∀ t : Fin 16, idx ⟨nqPerm t, ⟨t, rfl⟩⟩ = t := by
    intro t
    apply nqPerm_injective
    exact (hidx ⟨nqPerm t, ⟨t, rfl⟩⟩).symm
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥NQ →* Multiplicative (Fin 2 → F4),
      ∀ x : ↥NQ, χ x = Multiplicative.ofAdd (vecOf (idx x)) :=
    ⟨{ toFun := fun x => Multiplicative.ofAdd (vecOf (idx x))
       map_one' := by
         show Multiplicative.ofAdd (vecOf (idx 1)) = 1
         rw [hone, vecOf_zero, ofAdd_zero]
       map_mul' := fun x y => by
         show Multiplicative.ofAdd (vecOf (idx (x * y)))
           = Multiplicative.ofAdd (vecOf (idx x)) * Multiplicative.ofAdd (vecOf (idx y))
         rw [hmul, vecOf_xorF, ofAdd_add] }, fun x => rfl⟩
  have hχinj : Function.Injective χ := by
    intro x y h
    apply hinj
    apply vecOf_injective
    have h' : Multiplicative.ofAdd (vecOf (idx x)) = Multiplicative.ofAdd (vecOf (idx y)) :=
      (hχ x).symm.trans (h.trans (hχ y))
    exact Equiv.injective Multiplicative.ofAdd h'
  have hχsurj : Function.Surjective χ := by
    intro w
    obtain ⟨v, rfl⟩ := Equiv.surjective Multiplicative.ofAdd w
    obtain ⟨t, rfl⟩ := vecOf_surjective v
    refine ⟨⟨nqPerm t, ⟨t, rfl⟩⟩, ?_⟩
    rw [hχ, hself t]
  refine ⟨MulEquiv.ofBijective χ ⟨hχinj, hχsurj⟩, fun t => ?_⟩
  show χ ⟨nqPerm t, ⟨t, rfl⟩⟩ = _
  rw [hχ, hself t]

end CFSG.Quasithin.RonanH143
