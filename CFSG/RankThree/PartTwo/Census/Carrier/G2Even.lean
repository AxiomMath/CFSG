module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2EvenRank
public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.Blueprint.Catalog
public import CFSG.LieType.Chevalley.NativeMonomial
public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.Blueprint.ChevalleyPinned
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenShortCentralizer
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LieType.Chevalley.EvenRootCommutatorF4

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.G2Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Assembly.RankThreeEven

theorem threeRankLeOne_of_range {K : Type} [Field K] [CharP K 2] {G : Type*} [Group G]
    {X : Subgroup G} {ρ : SL2 K →* G} (hρ : ρ.range = X) (hρi : Function.Injective ρ) :
    ThreeRankLeOne X :=
  ThreeRankLeOne.of_eq hρ.symm
    (ThreeRankLeOne.of_mulEquiv (MonoidHom.ofInjective hρi).symm threeRankLeOne_SL2)

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem threeRankLeOne_long :
    ThreeRankLeOne (adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} :
      Subgroup (ModGL .G2 K)) := by
  obtain ⟨-, -, hQ2, hC, -, hLN, hQL, ⟨ρ, -, -, hρ, hρi⟩, -⟩ :=
    even_G2_highest_long_root_centralizer K
  exact ThreeRankLeOne.of_eq hC (ThreeRankLeOne.sup hQ2 hLN hQL (threeRankLeOne_of_range hρ hρi))

theorem threeRankLeOne_short :
    ThreeRankLeOne (adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2v 1} :
      Subgroup (ModGL .G2 K)) := by
  obtain ⟨-, -, hA2, hC, -, hLN, hAL, ⟨ρ, -, -, hρ, hρi⟩, -⟩ :=
    even_G2_highest_short_root_centralizer K
  have hA : IsPGroup 2 (g2ShortRadical K) := @CFSG.IsElementaryAbelian.isPGroup 2 _ _ hA2
  exact ThreeRankLeOne.of_eq hC (ThreeRankLeOne.sup hA hLN hAL (threeRankLeOne_of_range hρ hρi))

theorem localRank_three_adjointGroup : localRank 3 (adjointGroup .G2 K) ≤ 2 := by
  refine localRank_three_le_two_of_centralizers fun s hs => ?_
  rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) s hs with h | h
  · exact ThreeRankLeOne.centralizer_of_isConj h
      (ThreeRankLeOne.centralizer_of_le le_rfl (threeRankLeOne_long K))
  · exact ThreeRankLeOne.centralizer_of_isConj h
      (ThreeRankLeOne.centralizer_of_le le_rfl (threeRankLeOne_short K))

theorem localRank_three_adjointQuotient : localRank 3 (AdjointQuotient .G2 K) ≤ 2 := by
  have e : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot
  rw [localRank_eq_of_mulEquiv e Nat.prime_three]
  exact localRank_three_adjointGroup K

end CFSG.RankThree.PartTwo.Census.Carrier.G2Even

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem excluded433_G2_even (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp : q.p = 2) :
    Excluded433 (.lie ⟨.G2 q, hv⟩) := by
  intro G _ _ hG e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 q.exponent) = q.card := by
    rw [GaloisField.card 2 q.exponent q.exponent_pos.ne', PrimePower.card_def, hp]
  have : CharP (GaloisField 2 q.exponent) 2 := inferInstance
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp
    (GaloisField 2 q.exponent) hK
  exact hG.false_of_localRank_three_le_two (e.trans b.symm)
    (Carrier.G2Even.localRank_three_adjointQuotient (GaloisField 2 q.exponent))

end CFSG.RankThree.PartTwo.Census
