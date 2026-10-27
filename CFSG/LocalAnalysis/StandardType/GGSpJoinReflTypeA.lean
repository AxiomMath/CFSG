module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter

public section

namespace CFSG.StandardType.SpJoinRefl



section TypeA

variable {G : Type} [Group G]

theorem not_weylOfType_A_of_card {p n r : ℕ} {Bs : Subgroup G} {AL A' : Subgroup (MulAut ↥Bs)}
    (hn : 4 ≤ n) (hr : n + 1 ≤ r) (hr' : r ≤ n + 2)
    (hW : GGWeylOfType p (CoxeterMatrix.A r) A') (hAL : AL ≤ A')
    (hcard : Nat.card AL = 2 ^ n * n.factorial) : False := by
  obtain ⟨Ê, -⟩ := exists_permEquiv_of_ggWeylOfType_A hW
  have hA : Nat.card A' = (r + 1).factorial := by
    rw [← Nat.card_congr Ê.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
  have hdvd : 2 ^ n * n.factorial ∣ (r + 1).factorial := by
    rw [← hcard, ← hA]
    exact Subgroup.card_dvd_of_le hAL
  obtain ⟨k, hk3, hk⟩ : ∃ k, k ≤ 3 ∧ r + 1 = n + k := ⟨r + 1 - n, by omega, by omega⟩
  rw [hk] at hdvd
  exact not_two_pow_mul_factorial_dvd hn hk3 hdvd

end TypeA

end CFSG.StandardType.SpJoinRefl
