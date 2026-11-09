module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Tactic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenPermTable

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

public theorem a7_fixed_cyclic_five_certificate :
    ∀ x : ASevenCertificateGroup,
      (x ≠ 1 ∧ x ^ 5 = 1 ∧
        fixedSpanPow 5 x (a7a * x * a7a⁻¹)) →
      a7t * x = x * a7t := by
  intro x
  unfold fixedSpanPow
  simp only [ne_eq, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_one]
  simp only [← PermTable.enc_inj, PermTable.enc_mul, PermTable.enc_pow, PermTable.enc_one, PermTable.enc_a7a, PermTable.enc_a7a_inv, PermTable.enc_a7t]
  have hm := PermTable.enc_mem_permutations (x : Equiv.Perm (Fin 7))
  generalize PermTable.enc (x : Equiv.Perm (Fin 7)) = l at hm ⊢
  revert l
  refine PermTable.forall_mem_of_all ?_
  decide +kernel

end CFSG.GorensteinWalter
