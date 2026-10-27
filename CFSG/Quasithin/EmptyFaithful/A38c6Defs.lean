module

public import CFSG.Quasithin.EmptyFaithful.A38c5FmDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.A38c6

open CFSG.Quasithin.A38c5.Fm

@[expose] def BStab (B : Finset (Fin 8)) : Subgroup P8 where
  carrier := {g | ∀ x, g x ∈ B ↔ x ∈ B}
  mul_mem' := by
    intro g h hg hh x
    simp only [Equiv.Perm.mul_apply, hg (h x), hh x]
  one_mem' := fun x => Iff.rfl
  inv_mem' := by
    intro g hg x
    simpa using (hg (g⁻¹ x)).symm

@[expose] def dts (S : Finset (Fin 8)) : Set P8 :=
  {g | ∃ a b c d : Fin 8, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ({a, b, c, d} : Finset (Fin 8)) = S ∧ g = Equiv.swap a b * Equiv.swap c d}

@[expose] def Vsub (B : Finset (Fin 8)) : Subgroup P8 :=
  Subgroup.centralizer (dts B ∪ dts Bᶜ) ⊓ BStab B

@[expose] def cjP (γ : P8) (X : Subgroup P8) : Subgroup P8 := X.map (MulAut.conj γ).toMonoidHom

@[expose] def IsRegE8 (A : Subgroup P8) : Prop :=
  A ≤ alternatingGroup (Fin 8) ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a * a = 1) ∧
    Nat.card A = 8 ∧ ∀ i j : Fin 8, ∃! a : P8, a ∈ A ∧ a i = j

theorem mem_Vsub {B : Finset (Fin 8)} {g : P8} :
    g ∈ Vsub B ↔ (∀ c ∈ dts B ∪ dts Bᶜ, g * c = c * g) ∧ ∀ x, g x ∈ B ↔ x ∈ B := by
  unfold Vsub
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun c hc => (h1 c hc).symm, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun c hc => (h1 c hc).symm, h2⟩

end CFSG.Quasithin.A38c6
