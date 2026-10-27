
module

public import CFSG.Sporadic.Schreier.J4SOddLocalBase

public import CFSG.Sporadic.Schreier.J4SOddCheck
public import CFSG.Sporadic.Schreier.J4SOddLemmas
public import CFSG.Sporadic.Schreier.J4SThreeBase1
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native

section Local

variable {t : J}

theorem N_le_centralizer
    (ht : t ∈ N) : N ≤ Subgroup.centralizer {t} := fun n hn =>
  Subgroup.mem_centralizer_singleton_iff.2 (N_comm n hn t ht)

theorem N_conj_oddCoreImage (ht : t ∈ N) :
    ∀ n ∈ N, ∀ r ∈ oddCoreImage (Subgroup.centralizer {t}), n * r * n⁻¹ ∈
      oddCoreImage (Subgroup.centralizer {t}) :=
  fun _ hn _ hr => oddCoreImage_conj _ (N_le_centralizer ht hn) hr

end Local

theorem η_mul_self
    (a : ℕ) : η a * η a = 1 := by rw [← η_xor, Nat.xor_self, η_zero]

theorem orderOf_η
    {a : ℕ} (ha : a < 2048) (ha0 : a ≠ 0) : orderOf (η a) = 2 := by
  refine orderOf_eq_prime (by rw [sq, η_mul_self]) fun h => ha0 ?_
  exact η_injOn ha (by norm_num) (h.trans η_zero.symm)

end CFSG.Sporadic.J4Schreier
