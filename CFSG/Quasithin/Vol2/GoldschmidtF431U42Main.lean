module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AgMem

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def U42AutHalf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M₁ M₂ : Subgroup G) (z : G),
      IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups M₁ M₂) →
      pCoreOf 2 (M₁ ⊔ M₂) = ⊥ →
      z ^ 2 = 1 → z ≠ 1 → z ∈ centerOf (M₁ ⊓ M₂) →
      Subgroup.centralizer ({z} : Set G) ≤ M₁ →
      Subgroup.normalizer (centerOf (pCoreOf 2 M₁) : Set G) = M₁ →
      Subgroup.normalizer (centerOf (pCoreOf 2 M₂) : Set G) = M₂ →
      LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1

end CFSG.Quasithin.H13.F431.U42
