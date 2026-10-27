module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped Pointwise Matrix

variable {G : Type} [Group G] [Finite G]

@[expose] def IsMaximalParabolicOf (L X : Subgroup G) : Prop :=
  ParabolicOf L X ∧ X ≠ L ∧
    ∀ Y : Subgroup G, ParabolicOf L Y → X ≤ Y → Y ≠ L → Y = X

structure Ctx2311 (D : Data G) (Ch : Choice2011 G) extends Ctx23L D Ch where
  hSL3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn (Bar2 L) 3 (CFSG.Open.pRank 2 D.Z)
  X : Subgroup G
  hX : IsMaximalParabolicOf L X
  hTX : D.T ⊓ L ≤ X
  hXM : ¬ X ≤ D.M

namespace Ctx2311

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)

@[expose] def K : Subgroup G := Hinf (D.M ⊓ c.L)

@[expose] def W : Subgroup G := conjClosure c.X D.Z

@[expose] def I : Subgroup G := conjClosure c.L c.E

@[expose] def S : Subgroup G := CFSG.Open.pCoreOf 2 c.I

@[expose] def CME : Subgroup G := D.M ⊓ Subgroup.centralizer (c.E : Set G)

@[expose] def CMETilde : Subgroup G := CFSG.Quasithin.centralizerMod D.Z D.M c.E

abbrev MBarTilde : Type := ↥D.M ⧸ (c.CMETilde.subgroupOf D.M).normalCore

end Ctx2311

@[expose] def S23_11 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    ¬ CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn (Bar2 c.L) 3 (CFSG.Open.pRank 2 D.Z)

@[expose] def S23_12 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, (c.K.subgroupOf D.M).Normal

@[expose] def S23_13 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, Subgroup.normalizer (c.W : Set G) ≤ c.N

@[expose] def S23_14 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, frattini ↥c.E ≠ ⊥

@[expose] def S23_15_1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, (frattini ↥c.E).map c.E.subtype = D.Z

@[expose] def S23_15_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, CFSG.pCore 2 c.MBarTilde = ⊥

@[expose] def S23_16_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, c.E ≤ c.K ∧ c.I = c.L

@[expose] def S23_19 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch,
    CFSG.Quasithin.opResidual 2 c.CMETilde = CFSG.Quasithin.opResidual 2 c.CME

@[expose] def S23_20_1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, D.sig ∩ piSet c.CMETilde = ∅

@[expose] def S23_20_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, ∀ q : ℕ, q.Prime → q ≠ 2 →
    (1 < CFSG.Open.pRank q (⊤ : Subgroup (Bar2 D.M)) ∨
      1 < CFSG.Open.pRank q (barPreimage D.M (CFSG.pCore q (Bar2 D.M)))) →
    q ∉ piSet c.CMETilde

@[expose] def S23_21_1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx2311 D Ch,
    IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M))

@[expose] def S23_21_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx2311 D Ch,
    D.sig ∩ piSet (CFSG.fittingSubgroup (Bar2 D.M)) = ∅

end CFSG.LocalAnalysis.UniquenessCase.UC22
