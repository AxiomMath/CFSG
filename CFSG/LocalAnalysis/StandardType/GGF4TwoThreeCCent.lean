module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers
public import CFSG.RankThree.PartOne.KE.A1SL2

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


open scoped _root_.Classical in
@[expose] def GGF4TwoThreeCCentInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : adjointGroup .F4 K) (c : ModGL .F4 (AlgebraicClosure K))
      (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ),
      e ^ 3 = 1 → e ≠ 1 → c ∈ adjointGroup .F4 (AlgebraicClosure K) →
      rootDiagUnit .F4 a =
        c⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .F4 K) * c →
      ((rootFinset .F4).filter fun α => rootChar a α = 1).card = 12 →
        Group.IsSolvable (Subgroup.centralizer ({e} : Set (adjointGroup .F4 K)))

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
