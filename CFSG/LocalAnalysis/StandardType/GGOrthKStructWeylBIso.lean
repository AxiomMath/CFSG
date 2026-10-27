module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB

public section

namespace CFSG.StandardType

open CFSG.StandardType.SpJoin

theorem ggOrthKStruct_coxeterB_equiv {k : ℕ} (hk : 2 ≤ k) :
    ∃ e : (CoxeterMatrix.B k).Group ≃* ↥(spSignedGroup k 3),
      ∀ i : Fin k, ((e ((CoxeterMatrix.B k).simple i) : ↥(spSignedGroup k 3)) :
        Equiv.Perm (Fin k → Multiplicative (ZMod 3))) = spReflPerm k 3 i :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  ggRC_coxeterB_equiv_spSigned (p := 3) (by norm_num) hk

end CFSG.StandardType

end
