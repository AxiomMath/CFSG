module

public import CFSG.RankThree.PartOne.D4RC.Phi3
public import CFSG.RankThree.PartOne.SEITZ7.D4CentN
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.PSLDescent

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def Max3D4CentN6 : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K],
    IsoLie K (.trialityD4 q) → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ q.card ^ 2 - q.card + 1 →
      ∀ S : Sylow p K, ∀ E : Subgroup K, E ≤ S → CFSG.IsElementaryAbelian p E →
        Nat.card E = p ^ 2 →
        ∃ x ∈ E, x ≠ 1 ∧ ∀ N : Subgroup K, IsCoatom N → Subgroup.centralizer {x} ≤ N →
          ¬ Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ N


theorem max3D4CentN_of_phi6 (h : Max3D4CentN6) : Max3D4CentN := by
  intro q hq K _ _ _ hiso p hp hp5 hpd S E hES hE hEc
  rcases hpd with h3 | h6
  · exact rc3_centN_phi3 hq hiso hp hp5 h3 S E hES hE hEc
  · exact h q hq K hiso p hp hp5 h6 S E hES hE hEc

theorem exc3D4NonsplitPhi3Phi6_of_phi6 (h : Max3D4CentN6) : Exc3D4NonsplitPhi3Phi6 :=
  exc3D4NonsplitPhi3Phi6_of_centN (max3D4CentN_of_phi6 h)

end CFSG.RankThree.PartOne.D4RC
