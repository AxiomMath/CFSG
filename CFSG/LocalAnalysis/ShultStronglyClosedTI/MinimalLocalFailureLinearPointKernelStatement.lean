module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthStructure
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAbelianNormalizer
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type} [Group G]

@[expose] def LinearPointKernelConclusion (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (t : G) : Prop :=
  let B := pairPointStabilizer H beta
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  let K := minimalLocalFailureProperPairHull H z beta t
  let Q := minimalLocalFailurePairActionPointHull H z
  let q := Nat.card Q
  let J := Subgroup.centralizer (K : Set G)
  let C := H ⊓ Subgroup.centralizer (Q : Set G)
  let M := TwoCoreGrowth.pointTwoCoreImage H
  (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = q ∧
      Nonempty (K ≃* PSL2MatrixGroup k)) ∧
    (∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d) ∧
    B.relIndex H = q ^ 3 ∧
    Subgroup.normalizer (K : Set G) ⊓ H = Q ⊔ B ∧ Q ⊓ B = ⊥ ∧
    J = B ⊓ Subgroup.centralizer (Q : Set G) ∧
    Subgroup.normalizer (K : Set G) ⊓ C = Q ⊔ J ∧ Q ⊓ J = ⊥ ∧
      J ≤ Subgroup.centralizer (Q : Set G) ∧
    (Q ⊔ J).relIndex C ∣ q ^ 2 ∧
    (∃ f : J →* K, Function.Injective f) ∧
    (∀ u ∈ B, orderOf u = 2 → u ∈ J) ∧
    Q ≤ M ∧ Q ≤ Subgroup.centralizer (M : Set G) ∧
    TwoCoreGrowth.pointTwoCoreImage C = M ∧
    (∃ (k₀ : Type) (_ : Field k₀) (_ : Finite k₀), Nat.card k₀ = q ∧
      ∃ (φ : Q ≃* Multiplicative k₀) (ι : B →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀),
        ι.ker = J.subgroupOf B ∧
        (∀ (b : B) (x y : Q), (y : G) = (b : G) * x * (b : G)⁻¹ →
          (φ y).toAdd = ((ι b).left : k₀) * (ι b).right (φ x).toAdd) ∧
        (X.subgroupOf B).map ι = (SemidirectProduct.inl : k₀ˣ →* _).range) ∧
    ∀ y ∈ J, y ≠ 1 → Odd (orderOf y) →
      H ⊓ Subgroup.centralizer ({y} : Set G) = Q ⊔ (B ⊓ Subgroup.centralizer ({y} : Set G)) ∧
      TwoCoreGrowth.pointTwoCoreImage (H ⊓ Subgroup.centralizer ({y} : Set G)) = Q ∧
      M ⊓ Subgroup.centralizer ({y} : Set G) = Q

end CFSG.ShultStronglyClosedTI.LinearChain
