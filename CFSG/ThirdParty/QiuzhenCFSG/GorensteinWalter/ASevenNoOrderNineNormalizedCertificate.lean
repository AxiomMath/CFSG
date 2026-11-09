module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Tactic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenPermTable

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

public theorem a7_no_order_nine_normalized_by_t_certificate :
    ∀ x : A7OrderThree,
      ((x : ASevenCertificateGroup) * a7a = a7a * (x : ASevenCertificateGroup) ∧
        (x : ASevenCertificateGroup) ≠ a7a ∧
        (x : ASevenCertificateGroup) ≠ a7a ^ 2 ∧
        fixedSpanThree x a7a
          (a7t * (x : ASevenCertificateGroup) * a7t⁻¹)) → False := by
  rintro ⟨x, hx1, hx3⟩ h
  dsimp only at h
  revert hx1 hx3 h
  unfold fixedSpanThree
  simp only [ne_eq, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_one]
  simp only [← PermTable.enc_inj, PermTable.enc_mul, PermTable.enc_pow, PermTable.enc_one, PermTable.enc_a7a, PermTable.enc_a7t, PermTable.enc_a7t_inv]
  have hm := PermTable.enc_mem_permutations (x : Equiv.Perm (Fin 7))
  generalize PermTable.enc (x : Equiv.Perm (Fin 7)) = l at hm ⊢
  revert l
  refine PermTable.forall_mem_of_all ?_
  decide +kernel

end CFSG.GorensteinWalter
