module

public import CFSG.LocalAnalysis.StandardType.GGE6D4TwoNodeLocalInput
public import CFSG.LocalAnalysis.StandardType.GGTWSmallADefs
public import CFSG.LocalAnalysis.StandardType.GGTWSmallCarried
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4PackDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4Align
public import CFSG.LocalAnalysis.StandardType.GGDepED4UpOf
public import CFSG.LocalAnalysis.StandardType.GGDepED4UpClose
public import CFSG.LocalAnalysis.StandardType.GGDepED4Card
public import CFSG.LocalAnalysis.StandardType.GGPZE6Input
public import CFSG.LocalAnalysis.StandardType.GGResLeaves

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDepED4ZKInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G), GGResHyp 3 B Bs x L D J y K → ∀ labJ : LargeEvenLabel,
      LargeEvenInLambda2 labJ → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → labJ.tag = .D →
      labJ.rank = 4 → Nat.card ↥Bs = 3 ^ 6 → GGResSideDatum 3 Bs K J → y ∉ K

@[expose] def GGDepED4LowClose : Prop :=
  GGTBFixInput → GGTBFixNbrInput → GGPZE6Input →
  ∀ (G : Type) [Group G] [Finite G] (p k : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → x ∉ L →
    p = 3 → (k = 1 ∨ k = 2) → Nat.card ↥Bs = 3 ^ 6 →
    ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labX →
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → GGHasLabel labX (↥L ⧸ Subgroup.center ↥L) →
      ggRowTwoNodeSmall p labJ labX → (labX.tag = .E6 ∨ labX.tag = .twE6) →
      Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank → GGReflGenerated p (ggAutomizer J Bs) →
      GGTWHLAt p Bs L x → GGTWHLAt p Bs K y → GGDepED4Aligned p k Bs L J K → False

@[expose] def GGDepED4LowCloseK : Prop :=
  GGTBFixInput → GGTBFixNbrInput → GGPZE6Input →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → y ∉ K →
    p = 3 → Nat.card ↥Bs = 3 ^ 6 →
    ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labX →
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → GGHasLabel labX (↥K ⧸ Subgroup.center ↥K) →
      ggRowTwoNodeSmall p labJ labX → (labX.tag = .E6 ∨ labX.tag = .twE6) →
      Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank → GGReflGenerated p (ggAutomizer J Bs) →
      (Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y → GGTWHLAt p Bs K y) →
      GGTWHLAt p Bs L x → GGDepED4Aligned p 1 Bs K J L → False

theorem ggDepED4_close_up (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G]
    [Finite G] {p k : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hxL : x ∉ L) (hk : k = 1 ∨ k = 2) (hp3 : p = 3)
    (hCard : Nat.card ↥Bs = 3 ^ 7) (hA : GGDepED4Aligned p k Bs L J K) : False := by
  have hcfg := ggDepED4UpCfg_of_aligned hFix hFixK hH hxL hk hp3 hCard hA
  rcases hk with rfl | rfl
  · exact ggDepED4Up_false_one hcfg
  · exact ggDepED4Up_false_two hcfg

theorem ggDepED4_L_of_aligned (hLow : GGDepED4LowClose) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hPZ : GGPZE6Input) {G : Type} [Group G] [Finite G] {p k : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hxL : x ∉ L) (hk : k = 1 ∨ k = 2) (hp3 : p = 3)
    (hCard : Nat.card ↥Bs = 3 ^ 6 ∨ Nat.card ↥Bs = 3 ^ 7)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) (hJcard : Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank)
    (hRG : GGReflGenerated p (ggAutomizer J Bs))
    (hHL : Nat.card ↥Bs = 3 ^ 6 → GGTWHLAt p Bs L x)
    (hHK : Nat.card ↥Bs = 3 ^ 6 → GGTWHLAt p Bs K y) (hA : GGDepED4Aligned p k Bs L J K) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  exfalso
  rcases hCard with h6 | h7
  · exact hLow hFix hFixK hPZ G p k B Bs x L D J y K hH hxL hp3 hk h6 labJ labX hJΛ hXΛ hJl hXl
      hrow htag hJcard hRG (hHL h6) (hHK h6) hA
  · exact ggDepED4_close_up hFix hFixK hH hxL hk hp3 h7 hA

theorem ggDepED4_close_K (hLowK : GGDepED4LowCloseK) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hPZ : GGPZE6Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hyK : y ∉ K) (hp3 : p = 3)
    (hCard : Nat.card ↥Bs = 3 ^ 6 ∨ Nat.card ↥Bs = 3 ^ 7)
    {labJ labX : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) (hJcard : Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank)
    (hRG : GGReflGenerated p (ggAutomizer J Bs))
    (hHK : Nat.card ↥Bs = 3 ^ 6 → Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
      GGTWHLAt p Bs K y)
    (hHL : Nat.card ↥Bs = 3 ^ 6 → GGTWHLAt p Bs L x) (hA : GGDepED4Aligned p 1 Bs K J L) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hle := ggDepED4_card_le_oneNode hFix hH hp3 hA
  have h6 : Nat.card ↥Bs = 3 ^ 6 := by
    rcases hCard with h | h
    · exact h
    · rw [h] at hle
      norm_num at hle
  exact (hLowK hFix hFixK hPZ G p B Bs x L D J y K hH hyK hp3 h6 labJ labX hJΛ hXΛ hJl hXl hrow
    htag hJcard hRG (hHK h6) (hHL h6) hA).elim

end CFSG.StandardType

end
