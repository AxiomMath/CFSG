module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGResExactTwoOrthQTwoOn (R : ℕ → Prop) : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    GGInnerDiagOnLabel
        (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ R lab.rank) p Bs L ∧
      GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∧
      ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
        GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)

theorem ggResExactTwoOrthQTwoOn_or {R R' : ℕ → Prop} (h : GGResExactTwoOrthQTwoOn R)
    (h' : GGResExactTwoOrthQTwoOn R') : GGResExactTwoOrthQTwoOn fun r => R r ∨ R' r := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE ⟨hlab, hrest⟩
  have hlab' : GGInnerDiagOnLabel
      (fun p lab => (p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ R lab.rank) ∨
        (p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ R' lab.rank)) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨by
      obtain ⟨hp, ht, hn, hr⟩ := hP.1
      exact hr.elim (fun hr => Or.inl ⟨hp, ht, hn, hr⟩) (fun hr => Or.inr ⟨hp, ht, hn, hr⟩),
      hP.2⟩) hlab
  rcases hlab'.elim_or with hl | hl
  · exact h G p B Bs x L D J y K hH hF hS hE ⟨hl, hrest⟩
  · exact h' G p B Bs x L D J y K hH hF hS hE ⟨hl, hrest⟩

theorem GGResExactTwoOrthQTwoOn.mono {R R' : ℕ → Prop} (hRR : ∀ r, R' r → R r)
    (h : GGResExactTwoOrthQTwoOn R) : GGResExactTwoOrthQTwoOn R' := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE ⟨hlab, hrest⟩
  exact h G p B Bs x L D J y K hH hF hS hE
    ⟨largeEvenMarking_mono (fun _ _ _ _ _ _ hP =>
      ⟨⟨hP.1.1, hP.1.2.1, hP.1.2.2.1, hRR _ hP.1.2.2.2⟩, hP.2⟩) hlab, hrest⟩

end CFSG.StandardType
