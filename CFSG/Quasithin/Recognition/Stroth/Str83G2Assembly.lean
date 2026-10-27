module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartOne
public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseA3
public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseB4
public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseII3

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83_caseII1_false
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G)) : False := by
  by_cases hJ : jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S
  · exact str83_partOne_false hF hB ha hSz hL2 hII hZ2 hJ
  by_cases hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S
  · exact str83_partTwo_caseB_false hF hB ha hSz hL2 hII hZ2 hJ hZ
  · exact str83_partTwo_caseA_false hF hB ha hSz hL2 hII hZ2 hJ hZ

theorem str83CaseI_of_rqEq
    (hRq : Str83RqEq) :
    Str83CaseI := by
  intro G _ _ L1 L2 S a hF hB ha hSz hB2 h2
  have hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) := hRq G L1 L2 S a hF ha hSz hB2 h2
  by_contra hII
  by_cases hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G)
  · exact str83_caseII1_false hF hB ha hSz hL2 hII hZ2
  · exact str83_caseII2_false hF hB ha hSz hB2 h2 hII hZ2

end CFSG.Quasithin.Stroth

end
