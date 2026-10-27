module

public import CFSG.Quasithin.Recognition.HSTypeS6

public section

namespace CFSG.Quasithin.HSType

theorem actS6_swap01 : ∀ v : SpV, actS6 (Equiv.swap 0 1) v = v + spForm (spE 0) v • spE 0 := by
  decide

@[expose] def fpf0 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

theorem exists_conj_fpf : ∀ σ : Equiv.Perm (Fin 6), σ * σ = 1 → (∀ x, σ x ≠ x) →
    ∃ ρ : Equiv.Perm (Fin 6), ρ * σ * ρ⁻¹ = fpf0 := by
  decide +kernel

theorem centralizer_fpf_eq_comm : ∀ v : SpV, actS6 fpf0 v = v →
    ∃ u : SpV, v = actS6 fpf0 u + u := by
  decide +kernel

theorem fpf_of_odd_of_unipotent : ∀ σ : Equiv.Perm (Fin 6), σ * σ = 1 →
    Equiv.Perm.sign σ = -1 → σ ≠ Equiv.swap 0 1 →
    (∀ v : SpV, spForm (spE 0) v = 0 → actS6 σ v = v ∨ actS6 σ v = v + spE 0) →
      ∀ x, σ x ≠ x := by
  decide +kernel

end CFSG.Quasithin.HSType
