module

public import CFSG.Quasithin.Vol2.Ch11SecO8F
public import CFSG.Quasithin.Vol2.Ch11SecCB51Ord
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Quasithin

theorem factAStarSylow_holds : FactAStarSylow := by
  intro W _ _ hW n hn Hs Ks hKH hHN ⟨F, _, _, hF, ⟨e⟩⟩ h2 hO A hA
  have hAK := O8S.le_of_mem_aSet hW (by omega) hF hHN e hKH h2 hO hA
  have hP := O8S.isPGroup_of_isElemAbelian2 hA.2.2.1
  refine ⟨hAK, hP, ?_⟩
  have hcardK : Nat.card ↥Ks = 2 ^ n * (2 ^ (2 * n) - 1) := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
    simp [← pow_mul, mul_comm n 2]
  have hcardA := E3.card_eq_two_pow_mul hP (bot_le : (⊥ : Subgroup (MulAut W)) ≤ A)
  rw [Subgroup.card_bot, mul_one] at hcardA
  have hle := O8S.two_pow_le_card hA
  have hsub : Nat.card ↥(A.subgroupOf Ks) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hmul := Subgroup.index_mul_card (A.subgroupOf Ks)
  rw [hsub, hcardA, hcardK] at hmul
  have hodd : Odd (2 ^ (2 * n) - 1) := SecA.odd_two_pow_sub_one (by omega)
  have hmn : E3.mQuot A ⊥ ≤ n := B51.le_of_two_pow_dvd hodd (Dvd.intro_left _ hmul)
  have hnm : n ≤ E3.mQuot A ⊥ := by
    rw [hcardA] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  rw [le_antisymm hmn hnm, mul_comm] at hmul
  rw [Nat.eq_of_mul_eq_mul_left (by positivity) hmul]
  exact hodd.not_two_dvd_nat

end CFSG.Quasithin.Vol2.Ch11.SecC
