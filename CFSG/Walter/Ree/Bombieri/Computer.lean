module

public import CFSG.Walter.Ree.Bombieri.AppSpec
import CFSG.Walter.Ree.Bombieri.AppCert1
import CFSG.Walter.Ree.Bombieri.AppCert2
import CFSG.Walter.Ree.Bombieri.AppCert3
import CFSG.Walter.Ree.Bombieri.AppCert4
import CFSG.Walter.Ree.Bombieri.AppCert5
import CFSG.Walter.Ree.Bombieri.AppCert6

public section

namespace CFSG.Walter.Ree.Bombieri

variable {K : Type*} [Field K] [Fintype K] [CharP K 3]

theorem sq_eq_frob_of_le_ninetyNine
    {k : ℕ} (hk : 3 ≤ k) (hodd : k % 2 = 1) (hk99 : k ≤ 99)
    (hK : Fintype.card K = 3 ^ k) {σ : K ≃+* K} (hσ : IsThompsonAut K σ) :
    ∀ x, σ (σ x) = x ^ 3 := by
  rcases (by omega : k ≤ 69 ∨ (71 ≤ k ∧ k ≤ 79) ∨ (81 ≤ k ∧ k ≤ 87) ∨ (89 ≤ k ∧ k ≤ 91) ∨
      (93 ≤ k ∧ k ≤ 97) ∨ k = 99) with h | h | h | h | h | h
  · exact sq_eq_frob_of_appRange appOK_3_69 hk hodd hk h hK hσ
  · exact sq_eq_frob_of_appRange appOK_71_79 hk hodd h.1 h.2 hK hσ
  · exact sq_eq_frob_of_appRange appOK_81_87 hk hodd h.1 h.2 hK hσ
  · exact sq_eq_frob_of_appRange appOK_89_91 hk hodd h.1 h.2 hK hσ
  · exact sq_eq_frob_of_appRange appOK_93_97 hk hodd h.1 h.2 hK hσ
  · exact sq_eq_frob_of_appRange appOK_99_99 hk hodd h.ge h.le hK hσ

end CFSG.Walter.Ree.Bombieri
