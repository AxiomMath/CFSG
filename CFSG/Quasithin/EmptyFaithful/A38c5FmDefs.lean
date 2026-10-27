module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.A38c5.Fm

abbrev P8 : Type := Equiv.Perm (Fin 8)

@[expose] def partner (x : Fin 8) : Fin 8 := Fin.ofNat 8 (x.val ^^^ 1)

theorem partner_partner (x : Fin 8) : partner (partner x) = x := by revert x; decide

theorem partner_ne (x : Fin 8) : partner x ≠ x := by revert x; decide

theorem perm_apply_inv (g : P8) (x : Fin 8) : g (g⁻¹ x) = x := g.apply_symm_apply x

@[expose] def D8 : Subgroup P8 :=
  Subgroup.closure {Equiv.swap (0 : Fin 8) 1, Equiv.swap 2 3, Equiv.swap 4 5, Equiv.swap 6 7}

@[expose] def Smu : Subgroup P8 where
  carrier := {g | ∀ x, g (partner x) = partner (g x)}
  mul_mem' := by
    intro g h hg hh x
    simp only [Equiv.Perm.mul_apply, hh x, hg (h x)]
  one_mem' := fun x => rfl
  inv_mem' := by
    intro g hg x
    have h1 := hg (g⁻¹ x)
    rw [perm_apply_inv] at h1
    have h2 : g⁻¹ (partner x) = partner (g⁻¹ x) := by
      apply g.injective
      rw [perm_apply_inv, h1]
    exact h2

@[expose] def PStab (B : Finset (Fin 8)) : Subgroup P8 where
  carrier := {g | (∀ x, g x ∈ B ↔ x ∈ B) ∨ (∀ x, g x ∈ B ↔ x ∉ B)}
  mul_mem' := by
    intro g h hg hh
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · exact Or.inl fun x => by simp only [Equiv.Perm.mul_apply, hg (h x), hh x]
    · exact Or.inr fun x => by simp only [Equiv.Perm.mul_apply, hg (h x), hh x]
    · exact Or.inr fun x => by simp only [Equiv.Perm.mul_apply, hg (h x), hh x]
    · exact Or.inl fun x => by simp only [Equiv.Perm.mul_apply, hg (h x), hh x]; tauto
  one_mem' := Or.inl fun x => Iff.rfl
  inv_mem' := by
    intro g hg
    rcases hg with hg | hg
    · exact Or.inl fun x => by simpa using (hg (g⁻¹ x)).symm
    · exact Or.inr fun x => by
        have := hg (g⁻¹ x)
        simp only [perm_apply_inv] at this
        tauto

@[expose] def blocks3 : List (Finset (Fin 8)) := [{0, 1, 2, 3}, {0, 1, 4, 5}, {0, 1, 6, 7}]

end CFSG.Quasithin.A38c5.Fm
