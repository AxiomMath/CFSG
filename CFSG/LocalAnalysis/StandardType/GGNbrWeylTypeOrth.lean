module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
import CFSG.LocalAnalysis.StandardType.GGTorusWeylTypeEven
import CFSG.LocalAnalysis.StandardType.GGTorusWeylTypeSigned
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical
import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem ggWTB1_recipeOmegaPlus_evenWeylTypeW
    {l n p : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n + 1) (hle : Even l) (hl : 4 ≤ l) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_plus hl),
    ggTorusWeylTypeW_of_evenSignedPermEltSC (kP := fun k => k = l) hp hp2 (fun _ h => h) hZ hcp
      (fun k hk => by omega)
      (ggOrthEvenTorusInput_holds.1 K l p hl hp (Or.inr ⟨hle, by rw [hK]; exact hpn⟩))⟩

private theorem ggWTB1_recipeOmegaPlus_signedWeylTypeW
    {l n p : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n + 1) (hlo : Odd l) (hl : 5 ≤ l) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_plus (by omega)),
    ggTorusWeylTypeW_of_signedEltSC hp hp2 hZ (fun _ h _ => h) hcp
      (ggOrthSignedTorusInput_holds.1 K l p hl hlo hp (by rw [hK]; exact hpn))⟩

private theorem ggWTB1_recipeOmegaMinus_evenWeylTypeW
    {m n p : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n + 1) (hme : Even m) (hm : 4 ≤ m) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ m) hbc
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus (by omega) b c hbc),
    ggTorusWeylTypeW_of_evenSignedPermEltSC (kP := fun k => k = m + 1) hp hp2 (fun _ h => h) hZ hcp
      (fun k hk => by omega)
      (ggOrthEvenTorusInput_holds.2 K m p b c hm hme hbc hp (by rw [hK]; exact hpn))⟩

private theorem ggWTB1_recipeOmegaMinus_signedWeylTypeW
    {m n p : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1 ∨ (Odd m ∧ p ∣ 2 ^ n + 1)) (hm : 3 ≤ m)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hp2 : p ≠ 2 := by
    rcases hpn with h | ⟨-, h⟩
    · exact ne_two_of_dvd_two_pow_sub_one hn h
    · exact TableBU.ne_two_of_dvd_two_pow_add_one hn h
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 hm hbc
  refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus hm b c hbc),
    ggTorusWeylTypeW_of_signedEltSC hp hp2 hZ (fun _ h _ => h) hcp
      (ggOrthSignedTorusInput_holds.2 K m p b c hm hbc hp ?_)⟩
  rcases hpn with h | ⟨ho, h⟩
  · exact Or.inl (by rw [hK]; exact h)
  · exact Or.inr ⟨ho, by rw [hK]; exact h⟩

theorem ggNbrTableBWeylTypeNonSplitOn_orth :
    GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitOrthLabel := by
  rintro p hp hp2 ⟨tag, rank, n⟩ hlab hS - Q hQ
  have hn : 1 ≤ n := hlab.1
  apply nbrC_rawDatum_guard
  rcases hS with ⟨ht, hr, hpd⟩ | ⟨ht, hr, hpd⟩
  · simp only at ht hr hpd
    subst ht
    have h3 : rank ≠ 3 := by omega
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg h3] at hQ ⊢
    rcases Nat.even_or_odd rank with he | ho
    · exact ggWTB1_recipeOmegaPlus_evenWeylTypeW hp hn hpd he hr hQ
    · have h5 : 5 ≤ rank := by
        obtain ⟨k, hk⟩ := ho
        omega
      exact ggWTB1_recipeOmegaPlus_signedWeylTypeW hp hn hpd ho h5 hQ
  · simp only at ht hr hpd
    subst ht
    have h2 : rank ≠ 2 := by omega
    have h3 : rank ≠ 3 := by omega
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg h2, if_neg h3] at hQ ⊢
    rcases hpd with hpd | hpd
    · rcases Nat.even_or_odd (rank - 1) with he | ho
      · have h4 : 4 ≤ rank - 1 := by
          obtain ⟨k, hk⟩ := he
          omega
        exact ggWTB1_recipeOmegaMinus_evenWeylTypeW hp hn hpd he h4 hQ
      · exact ggWTB1_recipeOmegaMinus_signedWeylTypeW hp hn (Or.inr ⟨ho, hpd⟩) (by omega) hQ
    · exact ggWTB1_recipeOmegaMinus_signedWeylTypeW hp hn (Or.inl hpd) (by omega) hQ

end CFSG.StandardType

end
