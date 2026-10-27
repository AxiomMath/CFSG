module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoBasic
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReeF4Core

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.RankThree.PartTwo.Sec4.Item462AltProof

section ReeF4

open CFSG.LieType.Ree

theorem isQuasisimple_statedSU_three_odd_center {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    IsQuasisimple (CFSG.Open.StatedSU 3 (2 ^ f) F) ∧
      Odd (Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ f) F))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq : (3, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h' : 2 ^ f = 2 := (Prod.mk.inj h).2
    have h4 : 4 ≤ 2 ^ f :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨hq, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF le_rfl hnq
  refine ⟨hq, ?_⟩
  rw [hZ, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (by norm_num)).2.2]
  exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)

theorem reeGamma_not_pullDatum
    {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : MulAut (ReeTag.F4.reeGamma K a)) (hβ : orderOf β = 3) : ¬ PullDatum β := by
  intro hD
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hinj := conj_injective_of_center_eq_bot
    (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  by_cases hin : β ∈ (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut _).range
  ·
    obtain ⟨y, rfl, hy3, hy1⟩ := exists_conj_of_isInnerAut hinj hβ hin
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨eC⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU
      a K hK y (orderOf_eq_prime hy3 hy1)
    have hF : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
    obtain ⟨hq, hZ⟩ := isQuasisimple_statedSU_three_odd_center hF (by omega)
    refine hD.false_of_quasisimple_fixed (Subgroup.centralizer {y}) (fun x => ?_)
      (hq.of_mulEquiv eC) ?_
    · rw [conj_apply_eq_iff, Subgroup.mem_centralizer_singleton_iff, eq_comm]
    · rwa [Nat.card_congr (Subgroup.centerCongr eC).toEquiv]
  ·
    have hpow : β ^ 3 = 1 := hβ ▸ pow_orderOf_eq_one β
    have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have hq4 : (2 ^ (2 * a + 1)) ^ 4 % 3 = 1 := by
      rw [Nat.pow_mod, hq]
    have h1 : 1 ≤ (2 ^ (2 * a + 1)) ^ 4 := Nat.one_le_pow _ _ (by positivity)
    have hdvd : 3 ∣ (2 ^ (2 * a + 1)) ^ 4 - 1 := by omega
    exact hD.false_of_fieldCoreAt hinj
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.fieldCoreAt_reeGamma ha hK Nat.prime_three
        (by norm_num) hdvd β hpow hin)

end ReeF4

theorem kChevTwo_reeF4
    (n : ℕ) (hn : Odd n) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      Blueprint.ReeTitsModel X .twistedF4 2 n →
        ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ _ hm β hβ
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_reeGamma hm
  exact not_innThetaNoncyclic_of_mulEquiv e
    (center_eq_bot_of_mulEquiv e (CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial a K hK))
    (fun β' hβ' => reeGamma_not_pullDatum ha hK β' hβ') β hβ

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
