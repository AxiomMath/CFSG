module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGNbrTableBOrthPlus
import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly OrthNs OrthExc OrthExcEven

theorem recipeOmegaPlus_evenReflGenW
    {l n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n + 1) (hle : Even l) (hl : 4 ≤ l) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  obtain ⟨hZ, hcp⟩ := center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_plus hl),
    ggTorusReflGenW_of_evenSignedPermEltSC hp hp2 (fun _ h => h) hZ hcp
      (ggOrthEvenTorusInput_holds.1 K l p hl hp (Or.inr ⟨hle, by rw [hK]; exact hpn⟩))⟩

theorem recipeOmegaMinus_evenReflGenW
    {m n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n + 1) (hme : Even m) (hm : 4 ≤ m) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  obtain ⟨hZ, hcp⟩ := center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ m) hbc
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus (by omega) b c hbc),
    ggTorusReflGenW_of_evenSignedPermEltSC hp hp2 (fun _ h => h) hZ hcp
      (ggOrthEvenTorusInput_holds.2 K m p b c hm hme hbc hp (by rw [hK]; exact hpn))⟩

end CFSG.StandardType
