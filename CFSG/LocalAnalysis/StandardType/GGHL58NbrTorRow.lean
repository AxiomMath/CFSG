module

public import CFSG.LocalAnalysis.StandardType.GGHL58NbrSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDepED4KCovered (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (GGTBTorCov p lab ∧ ¬ GGTBWExcl lab ∧ ¬ GGOutdiagTwistedLabel lab) ∧ LargeEvenSplit p lab

theorem ggHL58Nbr_of_tbTor_row (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hW : GGTBWNormLabelInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hyK : y ∉ K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (h : GGInnerDiagOnLabel GGDepED4KCovered p Bs K) : GGTWHLAt p Bs K y := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  let S : ℕ → LargeEvenLabel → Prop := fun p lab => p ≠ 2 ∧ GGDepED4KCovered p lab
  have hW' : GGTBWNormInputNbr S :=
    ggTBWNormInputNbr_of_labels fun p lab hpp hlab hSlab =>
      hW p hpp hSlab.1 lab hlab hSlab.2.1.2.1 fun h => hSlab.2.1.2.2 (Or.inl h)
  have hCov : GGInnerDiagOnLabel GGTBTorCov p Bs K :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1.1.1, hP.2⟩) h
  have hM : GGInnerDiagOnLab S p Bs K :=
    largeEvenMarking_mono
      (fun lab R _ I F θ hP => ⟨⟨hp2, hP.1⟩, hP.1.2, hP.2.1, hP.2.2⟩) h
  have hWrows : GGTBTorWRows := ggTBTorWRows_of_all hT
  obtain ⟨m, N, C, M, hN, hom, hpm, -, -, hTor⟩ :=
    l05nPlP4_core_K hWrows hLift hH hCov
  exact ggHL58Nbr_of_torData hW' hH hCent hM hN hom hpm hTor

end CFSG.StandardType

end
