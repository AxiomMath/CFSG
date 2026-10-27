module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6RankAux
import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


private theorem q2cTE6R_seven_not_dvd (n : ℕ) : ¬ 7 ∣ 2 ^ n + 1 := by
  intro h
  have hz : ((2 : ZMod 7) ^ n + 1) = 0 := by
    have h' := (ZMod.natCast_eq_zero_iff (2 ^ n + 1) 7).2 h
    push_cast at h'
    exact h'
  have h2 : (2 : ZMod 7) ^ n = -1 := by
    linear_combination hz
  have h3 : ((2 : ZMod 7) ^ n) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm n 3, pow_mul]
    have h23 : (2 : ZMod 7) ^ 3 = 1 := by decide
    rw [h23, one_pow]
  rw [h2] at h3
  have hne : ((-1 : ZMod 7)) ^ 3 ≠ 1 := by decide
  exact hne h3

theorem q2c_twE6_rank {p d : ℕ} {lab : LargeEvenLabel} (hlab : lab.tag = .twE6) (hp : p.Prime)
    (hp2 : p ≠ 2) (hsplit : LargeEvenSplit p lab) (hpd : p ∣ d) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      (∀ r : ℕ, GGTorusLift p r R → p ^ r ≤ Nat.card A) →
      p ^ (d - 1) ≤ Nat.card A → Nat.card A ≤ p ^ d →
      (p = 3 ∧ d = 6) ∨ (p = 5 ∧ d = 5)) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hlab
  subst hlab
  have hpn : p ∣ 2 ^ n + 1 :=
    dvd_two_pow_add_one_of_split_twE6 (lab := ⟨.twE6, l, n⟩) rfl hsplit
  refine TwE6Delta.labelAll (lab := ⟨.twE6, l, n⟩) rfl (Q := fun R _ I =>
    ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
    (∀ r : ℕ, GGTorusLift p r R → p ^ r ≤ Nat.card A) →
    p ^ (d - 1) ≤ Nat.card A → Nat.card A ≤ p ^ d →
    (p = 3 ∧ d = 6) ∨ (p = 5 ∧ d = 5)) ?_
  intro K _ _ hK
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    simp only [pow_zero, one_pow] at hK
    haveI : Fintype K := Fintype.ofFinite K
    have h2 : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  intro A hA hAI hbig hlo hup
  by_cases hp3 : p = 3
  · subst hp3
    have hupper : Nat.card A ≤ 3 ^ 6 :=
      ggTwE6ThreeInndiagRankInput_holds K n hn hK hpn A hA hAI
    have hlower : 3 ^ 4 ≤ Nat.card A :=
      hbig 4 (ggTorusLift_twE6Three hn hK hpn)
    have hd_ge : 4 ≤ d :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hlower.trans hup)
    have hd_le : d ≤ 7 := by
      have h : d - 1 ≤ 6 :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hlo.trans hupper)
      omega
    left
    have hcases : d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact absurd hpd (by norm_num)
    · exact absurd hpd (by norm_num)
    · exact ⟨rfl, rfl⟩
    · exact absurd hpd (by norm_num)
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra hlt
      have hle : p ≤ 4 := by omega
      interval_cases p
      · exact absurd rfl hp2
      · exact absurd rfl hp3
      · exact absurd hp (by norm_num)
    have hupper : Nat.card A ≤ p ^ 6 :=
      ggTwE6Row_card_le_of_recipe hn hK hp hp3 hpn A hAI hA
    have hlift : GGTorusLift p 5 (TwE6Delta.RecipeR K n) := by
      have h := ggTorusLift_twE6Add_holds hn hK hp hpn
      rwa [TwE6Delta.liftRank_of_ne hp3] at h
    have hlower : p ^ 5 ≤ Nat.card A := hbig 5 hlift
    have hd_ge : 5 ≤ d :=
      (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlower.trans hup)
    have hd_le : d ≤ 7 := by
      have h : d - 1 ≤ 6 :=
        (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlo.trans hupper)
      omega
    have hcases : d = 5 ∨ d = 6 ∨ d = 7 := by omega
    rcases hcases with rfl | rfl | rfl
    · right
      exact ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpd, rfl⟩
    · exfalso
      have h23 : p ∣ 2 * 3 := by simpa using hpd
      rcases (Nat.Prime.dvd_mul hp).1 h23 with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
    · exfalso
      have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp hpd
      exact q2cTE6R_seven_not_dvd n (hp7 ▸ hpn)

end CFSG.StandardType
