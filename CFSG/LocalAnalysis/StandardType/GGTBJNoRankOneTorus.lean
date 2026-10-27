module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRankOne_linear_rank {G : Type} [Group G] [Finite G] {p m : ℕ} {x : G} {L : Subgroup G}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hpm : p ∣ 2 ^ m - 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hx : x ^ p = 1) (hx1 : x ≠ 1)
    (hL : commutator L = ⊤)
    (hlab : GGHasLabel (⟨.A, 2 * p - 1, m⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L)) :
    2 * p - 1 ≤ LargeEvenTwoLocalRank p G := by
  dsimp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeLinear] at hlab
  rw [show 2 * p - 1 + 1 = 2 * p by omega] at hlab
  obtain ⟨K, _, _, hK, hQ'⟩ := hlab
  haveI hchar : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpm
  obtain ⟨e⟩ := hQ'
  have h := succ_le_twoLocalRank_of_torusLift hp hLx hx hx1 hL
    (e.trans (TypeA.recipeEquiv (2 * p) K))
    (TypeA.ggTorusLift_sub_two (d := 2 * p) hp hpK (by omega)
      (TypeA.slHasSections_of_five_le (by omega)))
  omega

end CFSG.StandardType

end
