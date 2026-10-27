module

public import CFSG.LocalAnalysis.StandardType.GGTWHLCover
public import CFSG.LocalAnalysis.StandardType.GGHL58NbrTorRow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWKCovered2 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTWKCovered p lab ∨ GGDepED4KCovered p lab

@[expose] def GGHL58NbrTorRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N k : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → x ∉ L → y ∉ K →
    (k = 1 ∨ k = 2) → 3 ≤ p → p ∣ N → (N = 5 ∨ N = 6 ∨ N = 9) →
    Nat.card ↥Bs = p ^ (N - 1) → GGTWAligned p N k Bs L J K →
    Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
    ¬ GGInnerDiagOnLabel GGTWKCovered2 p Bs K → GGTWHLAt p Bs K y

theorem ggHL58NbrTorRestInput_of_rest (h : GGHL58NbrRestInput) : GGHL58NbrTorRestInput :=
  fun G _ _ p N k _ B Bs x L D J y K hH hxL hyK hk hp hpN hN hcard hA hCent hK =>
    h G p N k B Bs x L D J y K hH hxL hyK hk hp hpN hN hcard hA hCent
      (fun h1 => hK (largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨Or.inl hP.1, hP.2⟩) h1))

theorem ggHL58NbrRestInput_of_torrest (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hW : GGTBWNormLabelInput) (hRest : GGHL58NbrTorRestInput) : GGHL58NbrRestInput := by
  intro G _ _ p N k _ B Bs x L D J y K hH hxL hyK hk hp hpN hN hcard hA hCent hK
  by_cases hK2 : GGInnerDiagOnLabel GGDepED4KCovered p Bs K
  · exact ggHL58Nbr_of_tbTor_row hT hLift hW hH hyK hCent hK2
  · refine hRest G p N k B Bs x L D J y K hH hxL hyK hk hp hpN hN hcard hA hCent ?_
    intro hcov
    rcases GGInnerDiagOnLabel.elim_or (S := GGTWKCovered) (T := GGDepED4KCovered) hcov with h1 | h2
    · exact hK h1
    · exact hK2 h2

end CFSG.StandardType

end
