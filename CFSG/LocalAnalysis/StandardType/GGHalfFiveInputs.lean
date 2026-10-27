module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

@[expose] def GGNbrTablePNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ labJ labK : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labK →
      GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labK (K ⧸ Subgroup.center K) →
      ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labK' ∧
        GGTablePRow p labJ' labK' ∧
        GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧ GGHasLabel labK' (K ⧸ Subgroup.center K)

theorem GGNbrTablePNbrInput.toConfig (h : GGNbrTablePNbrInput) {G : Type} [Group G] [Finite G]
    (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) :
    GGNbrTablePConfig p B Bs x L D J :=
  fun hcfg hinn y K hnbr labJ labK hJ hK hhJ hhK =>
    h G p B Bs x L D J y K hcfg hinn.1 (hinn.2 y K hnbr) hnbr labJ labK hJ hK hhJ hhK

@[expose] def GGTableBAut48Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (N : Subgroup G), GGConfig 3 B Bs x L D J → GGNbr 3 B x D J y N → GGInnerDiagOn Bs N →
    ∀ labJ labN : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labN →
      GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labN (N ⧸ Subgroup.center N) →
      GGTablePRow 3 labJ labN → labJ = ⟨.A, 2, 2⟩ →
        StatedClassicalModel (↥N ⧸ Subgroup.center ↥N) .PSL 4 2 2 ∨
          48 ∣ Nat.card (ggAutomizer N Bs)

@[expose] def GGTableBAut48LeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (N : Subgroup G), GGConfig 3 B Bs x L D J → GGNbr 3 B x D J y N → GGInnerDiagOn Bs N →
    ∀ labJ labN : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labN →
      GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labN (N ⧸ Subgroup.center N) →
      GGTablePRow 3 labJ labN → labJ = ⟨.A, 2, 2⟩ →
        StatedClassicalModel (↥N ⧸ Subgroup.center ↥N) .PSL 4 2 2 ∨
          48 ≤ Nat.card (ggAutomizer N Bs)

theorem GGTableBAut48Input.toLe (h : GGTableBAut48Input) : GGTableBAut48LeInput := by
  intro G _ _ B Bs x L D J y N hcfg hnbr hinn labJ labN hΛJ hΛN hJ hN hrow hlab
  rcases h G B Bs x L D J y N hcfg hnbr hinn labJ labN hΛJ hΛN hJ hN hrow hlab with hm | hd
  · exact Or.inl hm
  · exact Or.inr (Nat.le_of_dvd Nat.card_pos hd)

@[expose] def GGTableBAut48OmegaInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (N : Subgroup G), GGConfig 3 B Bs x L D J → GGNbr 3 B x D J y N → GGInnerDiagOn Bs N →
    ∀ labJ labN : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labN →
      GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labN (N ⧸ Subgroup.center N) →
      GGTablePRow 3 labJ labN → labJ = ⟨.A, 2, 2⟩ → labN = ⟨.twD, 4, 2⟩ →
        StatedClassicalModel (↥N ⧸ Subgroup.center ↥N) .PSL 4 2 2 ∨
          48 ≤ Nat.card (ggAutomizer N Bs)

theorem GGTableBAut48Input.toOmega (h : GGTableBAut48Input) : GGTableBAut48OmegaInput := by
  intro G _ _ B Bs x L D J y N hcfg hnbr hinn labJ labN hΛJ hΛN hJ hN hrow hlab _
  exact h.toLe G B Bs x L D J y N hcfg hnbr hinn labJ labN hΛJ hΛN hJ hN hrow hlab

@[expose] def GGL44CenterTrivialInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsQuasisimple Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 4 2 2 → Subgroup.center Y = ⊥

end CFSG.StandardType

end
