module

public import Certificates.Certificate291130
public import CFSG.Monster.Existence.BabyOrder

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BScal

open CFSG.Blueprint CFSG.RankThree.PartOne.KS.ScalFive

theorem factorization_card_B_five :
    (Nat.card NativeSporadic.B).factorization 5 = 6 := by
  rw [CFSG.Monster.Existence.card_nativeB,
    show CFSG.Open.monsterBabyOrder = 5 ^ 6 * 265906014798491276235365154816 by
      unfold CFSG.Open.monsterBabyOrder; norm_num,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem bKernelTrivial
    (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* NativeSporadic.B)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hpg : IsPGroup 5 π.ker) :
    π.ker = ⊥ := by
  obtain ⟨q, z, s, t, h⟩ := Certificates.certificate291130
  exact h.kernelTrivial fiveSm_ne_one (by decide) (by decide) factorization_card_B_five.le π hπ hC
    hpg

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BScal
