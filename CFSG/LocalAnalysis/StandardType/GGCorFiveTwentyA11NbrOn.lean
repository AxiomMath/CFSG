module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGLabA8Seven (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ lab.rank = 8 ∧ lab.n = 1 ∧ p = 7

@[expose] def GGCorFiveTwentyA11CfgRootGenNbrInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGSecFiveA11ConfigWide p B Bs x L D J →
        ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGInnerDiagOnLabel S p Bs K →
          GGRootCompGenAvoiding p Bs K

theorem GGCorFiveTwentyA11CfgRootGenNbrInputOn.mono {S T : ℕ → LargeEvenLabel → Prop}
    (h : GGCorFiveTwentyA11CfgRootGenNbrInputOn S) (hTS : ∀ p lab, T p lab → S p lab) :
    GGCorFiveTwentyA11CfgRootGenNbrInputOn T :=
  fun G _ _ p B Bs x L D J hH hq hA y K hnb hK => h G p B Bs x L D J hH hq hA y K hnb
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hTS p _ hP.1, hP.2⟩) hK)

theorem ggCorFiveTwentyA11CfgRootGenNbrInputOn_of_split (S T : ℕ → LargeEvenLabel → Prop)
    (hST : GGCorFiveTwentyA11CfgRootGenNbrInputOn fun p lab => S p lab ∧ T p lab)
    (hSN : GGCorFiveTwentyA11CfgRootGenNbrInputOn fun p lab => S p lab ∧ ¬ T p lab) :
    GGCorFiveTwentyA11CfgRootGenNbrInputOn S := by
  intro G _ _ p B Bs x L D J hHyp hq hA y K hnb hK
  have hK' : GGInnerDiagOnLabel (fun p lab => (S p lab ∧ T p lab) ∨ (S p lab ∧ ¬ T p lab))
      p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨hs, hP⟩ =>
      ⟨(em (T p _)).elim (fun h => Or.inl ⟨hs, h⟩) (fun h => Or.inr ⟨hs, h⟩), hP⟩) hK
  rcases hK'.elim_or with h | h
  · exact hST G p B Bs x L D J hHyp hq hA y K hnb h
  · exact hSN G p B Bs x L D J hHyp hq hA y K hnb h

theorem ggCorFiveTwentyA11CfgRootGenNbrInput_of_on (S : ℕ → LargeEvenLabel → Prop)
    (hS : GGCorFiveTwentyA11CfgRootGenNbrInputOn S)
    (hN : GGCorFiveTwentyA11CfgRootGenNbrInputOn fun p lab => ¬ S p lab) :
    GGCorFiveTwentyA11CfgRootGenNbrInput := by
  intro G _ _ p B Bs x L D J hHyp hq hA y K hnb
  rcases ((hHyp.2.2.1.2 y K hnb).label S p).elim_or with h | h
  · exact hS G p B Bs x L D J hHyp hq hA y K hnb h
  · exact hN G p B Bs x L D J hHyp hq hA y K hnb h

end CFSG.StandardType

end
