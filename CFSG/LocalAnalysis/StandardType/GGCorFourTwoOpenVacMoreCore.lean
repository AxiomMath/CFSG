module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreVac
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB StdSubRestThree

@[expose] def GGCorFourTwoVacOn (V : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ¬ GGInnerDiagOnLab V p B L

namespace GGCorFourTwoVacOn

variable {U V W : ℕ → LargeEvenLabel → Prop}

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G}

theorem not_bstar (hV : GGCorFourTwoVacOn V) (hC : GGConfig p B Bs x L D J) :
    ¬ GGInnerDiagOnLab V p Bs L := fun hL =>
  hV G p B Bs x L D J hC (largeEvenMarking_mono (fun _ _ _ _ _ _ hP =>
    ⟨hP.1, hP.2.1, hC.2.1.1.trans hP.2.2.1, fun b hb => hP.2.2.2 b (hC.2.1.1 hb)⟩) hL)

theorem and_not (hV : GGCorFourTwoVacOn V) (hC : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLab U p B L) :
    GGInnerDiagOnLab (fun p lab => U p lab ∧ ¬ V p lab) p B L := by
  have hL' : GGInnerDiagOnLab (fun p lab => V p lab ∨ (U p lab ∧ ¬ V p lab)) p B L :=
    hL.mono fun p lab h => by
      by_cases hv : V p lab
      · exact Or.inl hv
      · exact Or.inr ⟨h, hv⟩
  rcases hL'.elim_or with h | h
  · exact (hV G p B Bs x L D J hC h).elim
  · exact h

theorem and_not_bstar (hV : GGCorFourTwoVacOn V) (hC : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLab U p Bs L) :
    GGInnerDiagOnLab (fun p lab => U p lab ∧ ¬ V p lab) p Bs L := by
  have hL' : GGInnerDiagOnLab (fun p lab => V p lab ∨ (U p lab ∧ ¬ V p lab)) p Bs L :=
    hL.mono fun p lab h => by
      by_cases hv : V p lab
      · exact Or.inl hv
      · exact Or.inr ⟨h, hv⟩
  rcases hL'.elim_or with h | h
  · exact (hV.not_bstar hC h).elim
  · exact h

end Config

theorem or (hV : GGCorFourTwoVacOn V) (hW : GGCorFourTwoVacOn W) :
    GGCorFourTwoVacOn fun p lab => V p lab ∨ W p lab := by
  intro G _ _ p B Bs x L D J hC hL
  rcases hL.elim_or with h | h
  · exact hV G p B Bs x L D J hC h
  · exact hW G p B Bs x L D J hC h

theorem mono (hV : GGCorFourTwoVacOn V) (hWV : ∀ p lab, W p lab → V p lab) :
    GGCorFourTwoVacOn W :=
  fun G _ _ p B Bs x L D J hC hL => hV G p B Bs x L D J hC (hL.mono hWV)

theorem bstarInnerDiag (hV : GGCorFourTwoVacOn V)
    (h : GGBstarInnerDiagLInputOn fun p lab => U p lab ∧ ¬ V p lab) :
    GGBstarInnerDiagLInputOn U := fun G _ _ p B Bs x L D J hC hL =>
  (h G p B Bs x L D J hC (hV.and_not hC hL)).mono fun _ _ h => h.1

theorem bstarInnerDiag_rest (hV : GGCorFourTwoVacOn V) (h : GGBstarInnerDiagLInputOn U) :
    GGBstarInnerDiagLInputOn fun p lab => U p lab ∧ ¬ V p lab :=
  fun G _ _ p B Bs x L D J hC hL =>
    hV.and_not_bstar hC (h G p B Bs x L D J hC (hL.mono fun _ _ h => h.1))

theorem transvectionCenter (hV : GGCorFourTwoVacOn V)
    (h : GGLTransvectionCenterInputOn fun p lab => U p lab ∧ ¬ V p lab) :
    GGLTransvectionCenterInputOn U := fun G _ _ p B Bs x L D J hC hL =>
  h G p B Bs x L D J hC (hV.and_not_bstar hC hL)

theorem noInvariantLine (hV : GGCorFourTwoVacOn V)
    (h : GGLNoInvariantLineInputOn fun p lab => U p lab ∧ ¬ V p lab) :
    GGLNoInvariantLineInputOn U := fun G _ _ p B Bs x L D J hC hL =>
  h G p B Bs x L D J hC (hV.and_not_bstar hC hL)

theorem tableBCx (hV : GGCorFourTwoVacOn V)
    (h : GGTableBCxInputOn fun p lab => U p lab ∧ ¬ V p lab) : GGTableBCxInputOn U :=
  fun G _ _ p B Bs x L D J hC hL => h G p B Bs x L D J hC (hV.and_not hC hL)

theorem tableBModule (hV : GGCorFourTwoVacOn V)
    (h : GGTableBModuleInputOn fun p lab => U p lab ∧ ¬ V p lab) : GGTableBModuleInputOn U :=
  fun G _ _ p B Bs x L D J hC hL => h G p B Bs x L D J hC (hV.and_not hC hL)

theorem tableBAction (hV : GGCorFourTwoVacOn V)
    (h : GGTableBActionInputOn fun p lab => U p lab ∧ ¬ V p lab) : GGTableBActionInputOn U :=
  fun G _ _ p B Bs x L D J B₂ hC hL => h G p B Bs x L D J B₂ hC (hV.and_not hC hL)

end GGCorFourTwoVacOn

namespace CorFourTwoVacMore

variable {S S' : ℕ → LargeEvenLabel → Prop}

theorem lTransvectionCenterInputOn_mono (hSS' : ∀ p lab, S p lab → S' p lab)
    (h : GGLTransvectionCenterInputOn S') : GGLTransvectionCenterInputOn S :=
  fun G _ _ p B Bs x L D J hC hL => h G p B Bs x L D J hC (hL.mono hSS')

theorem lNoInvariantLineInputOn_mono (hSS' : ∀ p lab, S p lab → S' p lab)
    (h : GGLNoInvariantLineInputOn S') : GGLNoInvariantLineInputOn S :=
  fun G _ _ p B Bs x L D J hC hL => h G p B Bs x L D J hC (hL.mono hSS')

end CorFourTwoVacMore

section Bounds

variable {V : ℕ → LargeEvenLabel → Prop}

theorem ggCorFourTwoVacOn_of_labelAll
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → V p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3) :
    GGCorFourTwoVacOn V :=
  fun _ _ _ _ _ _ _ _ _ _ hC hL => ggThmIHyp_false_of_labelAll h hC.1 hL

theorem ggCorFourTwoVacOn_of_lift
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → V p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => ∀ (L' : Type) [Group L']
        [Finite L'] (ψ : L' →* R), Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' →
        commutator L' = ⊤ → ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
          (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A < p ^ 3) :
    GGCorFourTwoVacOn V :=
  fun _ _ _ _ _ _ _ _ _ _ hC hL => CorFourTwoMore.false_of_labelAll_lift h hC hL

end Bounds

theorem ggCorFourTwoVacOn_tableBVac : GGCorFourTwoVacOn GGCorFourTwoTableBVacLabel := by
  have h1 : GGCorFourTwoVacOn fun p lab =>
      GGTwoThreeSmallLabel p lab ∨ GGTableBNbrInnerA2Label p lab :=
    ggCorFourTwoVacOn_of_labelAll fun p lab hp _ h _ => by
      rcases h with h | h
      · exact largeEvenLabelAll_card_lt_twoThreeSmall h
      · exact largeEvenLabelAll_card_lt_A2 hp h
  have h2 : GGCorFourTwoVacOn fun _ lab => lab.tag = .twA ∧ lab.rank = 2 :=
    ggCorFourTwoVacOn_of_lift fun _ _ hp hlab h hs =>
      largeEvenLabelAll_lift_card_lt_unitaryThree hp hlab h.1 h.2 hs
  exact (h1.or h2).mono fun p lab h => by
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

section TwF4


theorem ggCorFourTwoVacOn_twF4Three (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput) :
    GGCorFourTwoVacOn fun p lab => lab.tag = .twF4 ∧ p = 3 :=
  ggCorFourTwoVacOn_of_labelAll fun p lab hp hlab h hs => by
    obtain ⟨ht, rfl⟩ := h
    refine TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of ?_ hp hlab ht hs
    intro a ha K _ _ _ hK _ E hE
    exact hSR a ha K hK E hE

end TwF4

@[expose] def GGCorFourTwoVacMoreLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoTableBVacLabel p lab ∨ (lab.tag = .twF4 ∧ p = 3)

theorem ggCorFourTwoVacOn_vacMore
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput) :
    GGCorFourTwoVacOn GGCorFourTwoVacMoreLabel :=
  ggCorFourTwoVacOn_tableBVac.or (ggCorFourTwoVacOn_twF4Three hSR)

end CFSG.StandardType

end
