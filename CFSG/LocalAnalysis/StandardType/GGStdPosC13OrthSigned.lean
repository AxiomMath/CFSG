module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGStdPosC24Signed
import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly OrthNs OrthExc OrthExcEven

theorem recipeOmegaPlus_signedReflGenW
    {l n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n + 1) (hlo : Odd l) (hl : 5 ≤ l) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  obtain ⟨hZ, hcp⟩ := center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_plus (by omega)),
    ggTorusReflGenW_of_signedEltSC hp hp2 hZ (fun _ h _ => h) hcp
      (ggOrthSignedTorusInput_holds.1 K l p hl hlo hp (by rw [hK]; exact hpn))⟩

theorem recipeOmegaMinus_signedReflGenW
    {m n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n - 1 ∨ (Odd m ∧ p ∣ 2 ^ n + 1)) (hm : 3 ≤ m) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hp2 : p ≠ 2 := by
    rcases hpn with h | ⟨-, h⟩
    · exact ne_two_of_dvd_two_pow_sub_one hn h
    · exact TableBU.ne_two_of_dvd_two_pow_add_one hn h
  obtain ⟨hZ, hcp⟩ := center_data_omegaMinus (K := K) hp hp2 hm hbc
  refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus hm b c hbc),
    ggTorusReflGenW_of_signedEltSC hp hp2 hZ (fun _ h _ => h) hcp
      (ggOrthSignedTorusInput_holds.2 K m p b c hm hbc hp ?_)⟩
  rcases hpn with h | ⟨ho, h⟩
  · exact Or.inl (by rw [hK]; exact h)
  · exact Or.inr ⟨ho, by rw [hK]; exact h⟩

end CFSG.StandardType
