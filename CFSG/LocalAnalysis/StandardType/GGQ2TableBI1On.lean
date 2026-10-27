module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2TBSpLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ 4 ≤ lab.rank

@[expose] def GGQ2TBULabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 4 ≤ lab.rank ∧ ¬ 3 ∣ lab.rank + 1

@[expose] def GGQ2TBOmegaLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∧ Even lab.rank ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ Odd lab.rank ∧ 4 ≤ lab.rank)

@[expose] def GGQ2TBExcLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8

@[expose] def GGQ2TableBI1FailOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J → ∀ [Fact p.Prime],
      GGInnerDiagOnLabel (fun p lab => GGLabQTwo p lab ∧ S lab) p Bs L →
      ∃ labL : LargeEvenLabel, GGLabQTwo p labL ∧ GGQ2TBLabel labL ∧
        LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) ∧
        ∃ M : GGQ2LDatum p Bs L x, GGQ2LabelWeyl labL M.coxeter ∧ M.Shape ∧
          (Module.finrank (ZMod p) M.V ≤ Fintype.card M.Λ →
            (labL.tag = .twA ∧ 3 ∣ labL.rank + 1) ∨ labL.tag = .twE6)

theorem GGQ2TableBI1FailOn.mono {S T : LargeEvenLabel → Prop} (hST : ∀ lab, S lab → T lab)
    (h : GGQ2TableBI1FailOn T) : GGQ2TableBI1FailOn S := by
  intro G _ _ p B Bs x L D J hset hp hI1 _ hM
  exact h hset hp hI1 (largeEvenMarking_mono
    (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.1, hST _ hP.1.2⟩, hP.2⟩) hM)

theorem GGQ2TableBI1FailOn.or {S T : LargeEvenLabel → Prop} (hS : GGQ2TableBI1FailOn S)
    (hT : GGQ2TableBI1FailOn T) : GGQ2TableBI1FailOn fun lab => S lab ∨ T lab := by
  intro G _ _ p B Bs x L D J hset hp hI1 _ hM
  have hM' : GGInnerDiagOnLabel
      (fun p lab => (GGLabQTwo p lab ∧ S lab) ∨ (GGLabQTwo p lab ∧ T lab)) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2.imp (⟨hP.1.1, ·⟩) (⟨hP.1.1, ·⟩),
      hP.2⟩) hM
  rcases GGInnerDiagOnLabel.elim_or hM' with h | h
  · exact hS hset hp hI1 h
  · exact hT hset hp hI1 h

theorem ggQ2TableBI1Fail_of_on {S : LargeEvenLabel → Prop} (hS : GGQ2TableBI1FailOn S)
    (hN : GGQ2TableBI1FailOn fun lab => ¬ S lab) : GGQ2TableBI1Fail := by
  intro G _ _ p B Bs x L D J hset hp hI1 _
  have hM : GGInnerDiagOnLabel (fun p lab => GGLabQTwo p lab ∧ (S lab ∨ ¬ S lab)) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1, em _⟩, hP.2⟩) hset.2.1
  exact (hS.or hN) hset hp hI1 hM

end CFSG.StandardType

end
