module

public import CFSG.Quasithin.EmptyFaithful.R3c12Red
public import CFSG.Quasithin.EmptyFaithful.R3c12A6
public import CFSG.Quasithin.EmptyFaithful.R3c12U33
public import CFSG.Quasithin.EmptyFaithful.R3c12L4
public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.Quasithin.Background.A318PL3Unit
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.FFC4Res
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.EmptyFaithful.R3c9Elim
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.Quasithin.R3c10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open scoped commutatorElement

section Cases

@[expose] def Lemma115LieHighRest2 (X : Type) [Group X] : Prop :=
  ((∃ f : ℕ, (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)) ∨
    ReeTitsModel X .Tits 2 1) ∨ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 5 2 1

theorem lemma115LieHighRest_cases_rest2 {X : Type} [Group X] (h : Lemma115LieHighRest X) :
    Lemma115LieHighRest2 X ∨ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 4 2 1 ∨
      Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1 := by
  rcases h with (((⟨f, hfam⟩ | hTits) | ⟨n, hn, hm⟩) | ⟨⟨e⟩⟩ | hU33)
  · exact Or.inl (Or.inl (Or.inl ⟨f, hfam⟩))
  · exact Or.inl (Or.inl (Or.inr hTits))
  · rcases hn with rfl | rfl
    · exact Or.inr (Or.inl hm)
    · exact Or.inl (Or.inr hm)
  · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  · exact Or.inr (Or.inr (Or.inr hU33))

end Cases

section Residue

@[expose] def Input15335CloseLieRest2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieHighRest2 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15335CloseLieRest_of_rest2 (h113 : StageLemma14113) (kR : Input15335CloseLieRest2) :
    Input15335CloseLieRest := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hRest
  rcases lemma115LieHighRest_cases_rest2 hRest with h2 | h4 | ⟨⟨φ⟩⟩ | hU
  · exact kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL h2
  · exact R3c12.not_clConfig_of_psl4 h4 (R3c12.clConfig_of_ctx2 h113 c hN hYL)
  · exact R3c12.not_clConfig_of_alt6 φ (R3c12.clConfig_of_ctx2 h113 c hN hYL)
  · exact R3c12.not_clConfig_of_u33 hU (R3c12.clConfig_of_ctx2 h113 c hN hYL)

end Residue

end CFSG.Quasithin.R3c10
