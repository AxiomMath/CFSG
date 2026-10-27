module

public import CFSG.Blueprint.NativeSporadic
import CFSG.GH74.KGroups.M11

public section

open CFSG.GH74.KGroups

namespace Certificates

theorem certificate8037 : ∀ x ∈ CFSG.Blueprint.NativeSporadic.M11, x ^ 3 = 1 → x ≠ 1 →
    Nat.card ↥(CFSG.Blueprint.NativeSporadic.M11 ⊓
      Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 11)))) = 18 := by
  refine fun x hx hx3 hx1 => ?_
  obtain ⟨g, hg, rfl⟩ := M11.three_conj x hx (orderOf_eq_prime hx3 hx1)
  rw [card_inf_centralizer_eq, centCard_conj _ _ _ (normal_iff_of_mem hg),
    Certificates.certificate5125.2.2.2.2.2.2.2.2.1]

end Certificates
