module

public import Mathlib.Data.Finite.Perm

public section

namespace CFSG

namespace FiveTransitive.OrbitComplementCardBound
open MulAction

theorem card_le_factorials
    {E : Type*} [Finite E] (B : Subgroup (Equiv.Perm E)) (x : E) :
    Nat.card B ≤ (Nat.card (orbit B x)).factorial *
      (Nat.card E - Nat.card (orbit B x)).factorial := by
  classical
  let O : SubMulAction B E :=
    { carrier := orbit B x
      smul_mem' := by intro b y hy; exact mem_orbit_of_mem_orbit b hy }
  let C := Oᶜ
  let f := (toPermHom B O).prod (toPermHom B C)
  have hi : Function.Injective f := by
    intro b c he
    apply Subtype.ext
    apply Equiv.ext
    intro y
    by_cases hy : y ∈ orbit B x
    · exact congrArg (fun p : Equiv.Perm O × Equiv.Perm C => (p.1 ⟨y,hy⟩).val) he
    · exact congrArg (fun p : Equiv.Perm O × Equiv.Perm C => (p.2 ⟨y,hy⟩).val) he
  have hb := Nat.card_le_card_of_injective f hi
  rw [Nat.card_prod,Nat.card_perm,Nat.card_perm] at hb
  have hc : Nat.card C = Nat.card E - Nat.card (orbit B x) := by
    change Nat.card ((orbit B x)ᶜ : Set E) = _
    rw [Nat.card_coe_set_eq,Set.ncard_compl,← Nat.card_coe_set_eq]
  change Nat.card B ≤ (Nat.card (orbit B x)).factorial * (Nat.card C).factorial at hb
  rwa [hc] at hb

end FiveTransitive.OrbitComplementCardBound

end CFSG
