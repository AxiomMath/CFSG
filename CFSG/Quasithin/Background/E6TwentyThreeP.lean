module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E6TwentyThreeJ

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem card_le_twoPart_centralizer {Y S : Subgroup G} {a : G} (hSY : S ≤ Y)
    (hS2 : IsPGroup 2 S) (haS : ∀ s ∈ S, a * s = s * a) :
    Nat.card S ≤ 2 ^ (Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Y ⊓ Subgroup.centralizer ({a} : Set G) with hK
  have hSK : S ≤ K := fun s hs =>
    ⟨hSY hs, Subgroup.mem_centralizer_singleton_iff.mpr (haS s hs).symm⟩
  have hS2' : IsPGroup 2 (S.subgroupOf K) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  obtain ⟨P, hP⟩ := hS2'.exists_le_sylow
  have h1 : Nat.card (S.subgroupOf K) ≤ Nat.card P := Subgroup.card_le_of_le hP
  rw [Sylow.card_eq_multiplicity P, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]
    at h1
  exact h1

end CFSG.Quasithin.E6
