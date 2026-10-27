module

public import CFSG.LocalAnalysis.StandardType.GGResTwoSettled
public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGResMultiNodeRestTwoCellInput.or {S T : ℕ → LargeEvenLabel → Prop}
    (hS : GGResMultiNodeRestTwoCellInput S) (hT : GGResMultiNodeRestTwoCellInput T) :
    GGResMultiNodeRestTwoCellInput fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L D J y K hH _ hF hSt hE ⟨hL2, hnL, hK, hM, hrest⟩
  rcases GGInnerDiagOnLabel.elim_or hM with hM | hM
  · exact hS G p B Bs x L D J y K hH hF hSt hE ⟨hL2, hnL, hK, hM, hrest⟩
  · exact hT G p B Bs x L D J y K hH hF hSt hE ⟨hL2, hnL, hK, hM, hrest⟩

theorem GGResMultiNodeRestTwoCellInput.mono {S T : ℕ → LargeEvenLabel → Prop}
    (hST : ∀ p lab, S p lab → T p lab) (hT : GGResMultiNodeRestTwoCellInput T) :
    GGResMultiNodeRestTwoCellInput S := by
  intro G _ _ p B Bs x L D J y K hH _ hF hSt hE ⟨hL2, hnL, hK, hM, hrest⟩
  exact hT G p B Bs x L D J y K hH hF hSt hE
    ⟨hL2, hnL, hK, largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hST _ _ hP.1, hP.2⟩) hM, hrest⟩

theorem GGResMultiNodeRestTwoCellInput.of_false {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      GGInnerDiagOnLabel S p Bs L → GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny → False) :
    GGResMultiNodeRestTwoCellInput S := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ ⟨hL2, _, _, hM, _⟩
  exact (h G p B Bs x L D J y K hH hM hL2).elim

theorem ggResMultiNodeRestTwoCellInput_spSplit_four_five :
    GGResMultiNodeRestTwoCellInput (fun p lab =>
      (lab.tag = .B ∨ lab.tag = .C) ∧ (4 ≤ lab.rank ∧ lab.rank ≤ 5) ∧
        p ∣ 2 ^ lab.n - 1) := by
  apply GGResMultiNodeRestTwoCellInput.of_false
  intro G _ _ p _ B Bs x L D J y K hH hmark h2
  exact hH.false_of_exact2_L_spSplit_four_five hmark h2

theorem ggResMultiNodeRestTwoSettledInput_of_cell (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} (hcov : ∀ p lab, ggTwoResidualLabelL p lab → S p lab)
    (h : GGResMultiNodeRestTwoCellInput S) : GGResMultiNodeRestTwoSettledInput :=
  ggResMultiNodeRestTwoSettledInput_of_census hRig (h.mono hcov)

@[expose] def ggTwoCellClassical (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank ≤ 5) ∨ lab.tag = .D ∨ lab.tag = .twD) ∧
    3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggTwoCellTwD (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ (p = 3 ∧ lab.n = 1)

@[expose] def ggTwoCellExc (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1) ∨
    ((lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ p = 3 ∧ lab.n = 1)

@[expose] def ggTwoCellTwE6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1

theorem ggResMultiNodeRestTwoSettledInput_of_cells (hRig : GGLabelRigidInput)
    (hC : GGResMultiNodeRestTwoCellInput ggTwoCellClassical)
    (hD : GGResMultiNodeRestTwoCellInput ggTwoCellTwD)
    (hE : GGResMultiNodeRestTwoCellInput ggTwoCellExc)
    (hT : GGResMultiNodeRestTwoCellInput ggTwoCellTwE6) :
    GGResMultiNodeRestTwoSettledInput :=
  ggResMultiNodeRestTwoSettledInput_of_cell hRig (fun _ _ h => h)
    (hC.or (hD.or (hE.or hT)))

end CFSG.StandardType

end
