module

public import CFSG.LocalAnalysis.StandardType.GGDepED4ReadDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowOf
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowOfK
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowLeaf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDepED4_false_two_L (hcells : GGDepED4LowCells) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hPZ : GGPZE6Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hxL : x ∉ L) (hp3 : p = 3)
    (hCard : Nat.card ↥Bs = 3 ^ 6 ∨ Nat.card ↥Bs = 3 ^ 7)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) (hJcard : Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank)
    (hRG : GGReflGenerated p (ggAutomizer J Bs)) (hA : GGDepED4Aligned p 2 Bs L J K) : False := by
  rcases hCard with h6 | h7
  · exact ggDepED4Low_leaf hPZ (Or.inr rfl) hp3 hH hJΛ hXΛ hJl hXl hrow htag h6 hJcard hRG hcells
      (Or.inl ⟨rfl, ggDepED4LowCfg_of_aligned hFix hFixK hH hxL (Or.inr rfl) hp3 h6
        (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num)) hA⟩)
  · exact ggDepED4_close_up hFix hFixK hH hxL (Or.inr rfl) hp3 h7 hA

theorem ggDepED4_false_two_K (hcells : GGDepED4LowCells) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hPZ : GGPZE6Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hyK : y ∉ K) (hp3 : p = 3)
    (hCard : Nat.card ↥Bs = 3 ^ 6)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) (hJcard : Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank)
    (hRG : GGReflGenerated p (ggAutomizer J Bs)) (hA : GGDepED4Aligned p 2 Bs K J L) : False :=
  ggDepED4Low_leaf hPZ (Or.inr rfl) hp3 hH hJΛ hXΛ hJl hXl hrow htag hCard hJcard hRG hcells
    (Or.inr ⟨rfl, ggDepED4LowCfg_of_alignedK hFix hFixK hH hyK hp3 hCard
      (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num)) hA⟩)

end CFSG.StandardType

end
