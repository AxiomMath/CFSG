module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Tim79aCitedInvol

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.Open

theorem parrottFi22Statement_of_theorem4_theorem5
    (h4 : ∀ (G : Type) [Group G] [Finite G] (z : G), Tim79a.ParrottHyp z →
      centerIn (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) =
        centerIn (Subgroup.centralizer ({z} : Set G)) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ → Tim79a.ParrottCaseII z)
    (h5 : ∀ (G : Type) [Group G] [Finite G] (z : G), Tim79a.ParrottHyp z →
      centerIn (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) ≠
        centerIn (Subgroup.centralizer ({z} : Set G)) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22) :
    Tim79a.ParrottFi22Statement := by
  intro G _ _ z hz
  by_cases h1 : Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G = ⊤
  · exact Or.inl h1
  · by_cases hZ : centerIn (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) =
        centerIn (Subgroup.centralizer ({z} : Set G))
    · exact Or.inr (Or.inl (h4 G z hz hZ h1))
    · exact Or.inr (Or.inr (h5 G z hz hZ h1))

end CFSG.RankThree.GF2n.Tim79a
