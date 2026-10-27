module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreThreeTransp
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreDisconnected
import CFSG.Goldschmidt75.OddCore
public import CFSG.Fischer.Classification.Basic.Trichotomy

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open

theorem oddTranspCoreSimpleInput_holds :
    OddTranspCoreSimpleInput := by
  intro Y _ _ t hP hZ h2 hO
  have h3 : ∀ N : Subgroup Y, N.Normal → IsPGroup 3 N → N = ⊥ := fun N hN hN3 => by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hN3
    have hodd : Odd (Nat.card N) := by rw [hk]; exact Odd.pow (by decide)
    exact le_bot_iff.mp (hO ▸ CFSG.Goldschmidt75.le_oddCore hN hodd)
  by_cases hc : (commGraph {x : Y | IsConj t x}).Connected
  · exact CoreStar.permOrStar_of_hyp hP hZ
      (CFSG.Fischer.Classification.Pair.isSimpleGroup_commutator_of_connected hP hZ h2 h3 hc)
  · exact Or.inr (CoreStar.hasCoreStar_of_not_connected hP hZ h2 hO hc)

end CFSG.LocalAnalysis.WeakClosure81
