module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACLinFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQTwoVACCellOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → p = 3 → GGInnerDiagOnLabel S p Bs L →
      ¬ 4 ∣ Nat.card (ggAutomizer J Bs) → GGQTwoVACConcl p B Bs x L D J

@[expose] def GGQ2VACLabSymp (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLabQTwo p lab ∧ (lab.tag = .B ∨ lab.tag = .C)

@[expose] def GGQ2VACLabOrth (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLabQTwo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD)

@[expose] def GGQ2VACLabUnit (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLabQTwo p lab ∧ lab.tag = .twA

@[expose] def GGQ2VACLabExc (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLabQTwo p lab ∧ (lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
    lab.tag = .twE6)

@[expose] def GGQ2VACLabSmall (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLabQTwo p lab ∧ (lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der ∨
    lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4)

theorem ggQTwoVACCell_of_families (hA : GGQTwoVACCellOn GGQ2VACLabLin)
    (hBC : GGQTwoGuardFailsOn GGQ2VACLabSymp) (hD : GGQTwoGuardFailsOn GGQ2VACLabOrth)
    (hU : GGQTwoGuardFailsOn GGQ2VACLabUnit) (hE : GGQTwoGuardFailsOn GGQ2VACLabExc)
    (hSm : GGQTwoGuardFailsOn GGQ2VACLabSmall) : GGQTwoVACCell := by
  intro G _ _ p B Bs x L D J hS hp h4
  have hL : GGInnerDiagOnLabel (fun p lab => GGQ2VACLabLin p lab ∨ GGQ2VACLabSymp p lab ∨
      GGQ2VACLabOrth p lab ∨ GGQ2VACLabUnit p lab ∨ GGQ2VACLabExc p lab ∨
      GGQ2VACLabSmall p lab) p Bs L := by
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ h => ⟨?_, h.2⟩) hS.2.1
    obtain ⟨t, r, n⟩ := lab
    have hq : GGLabQTwo p ⟨t, r, n⟩ := h.1
    cases t <;> simp [GGQ2VACLabLin, GGQ2VACLabSymp, GGQ2VACLabOrth, GGQ2VACLabUnit,
      GGQ2VACLabExc, GGQ2VACLabSmall, hq]
  rcases hL.elim_or with hL | hL
  · exact hA G p B Bs x L D J hS hp hL h4
  rcases hL.elim_or with hL | hL
  · exact absurd (hBC G p B Bs x L D J hS hp hL) h4
  rcases hL.elim_or with hL | hL
  · exact absurd (hD G p B Bs x L D J hS hp hL) h4
  rcases hL.elim_or with hL | hL
  · exact absurd (hU G p B Bs x L D J hS hp hL) h4
  rcases hL.elim_or with hL | hL
  · exact absurd (hE G p B Bs x L D J hS hp hL) h4
  · exact absurd (hSm G p B Bs x L D J hS hp hL) h4

theorem ggQTwoI1_of_eq {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hB : B = Bs) :
    GGQTwoI1 Bs D J := by
  intro b hb hbJ
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hS.1.1.2.2.1.2.2.2.2.2.2
  rw [hD]
  exact ⟨by rw [hB]; exact hb, Subgroup.mem_centralizer_iff.mpr fun j hj => (hbJ j hj).symm⟩

theorem ggQTwoK1_of_eq {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hB : B = Bs) :
    GGQTwoK1 p B Bs x D J := by
  intro y K hnbr b hb hbK
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn (hS.1.2.2.1.2 y K hnbr)
  exact (hnbr.1.2.2.2.2.2 b).mp ⟨by rw [hB]; exact hb, hN hb, hbK⟩

end CFSG.StandardType

end
