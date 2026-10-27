module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs
public import CFSG.RankThree.PartTwo.Sec12.Hering129GFinal

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

section Classes

@[expose] def IsG2D4 (X : Type) [Group X] (r : TauCeti.PrimePower) (δ : ℕ) : Prop :=
  (δ = 1 ∧ Sec4.IsoGTwo X r) ∨
    (δ = 3 ∧ ∃ hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid,
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group))

variable {X : Type} [Group X] [Finite X]

@[expose] def IsThreeA (z : X) (r : ℕ) : Prop :=
  orderOf z = 3 ∧ z ∈ resCent (⊤ : Subgroup X) z ∧
    Sec4.IsSLThreePiAt ↥(resCent (⊤ : Subgroup X) z) r

@[expose] def IsThreeB (z : X) (s : ℕ) : Prop :=
  orderOf z = 3 ∧
    ComponentClassification.HarrisLit.IsSLTwoOver s ↥(resCent (⊤ : Subgroup X) z)

end Classes

@[expose] def KS129OTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SectionFourHyp X → Group.IsPerfect X →
    ((∃ r : TauCeti.PrimePower, Sec4.IsoGTwo (X ⧸ aschbacherSolvableCore 3 X) r) ∨
      (∃ (r : TauCeti.PrimePower) (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid),
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃*
          (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group)) ∨
      (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
        Sec4.IsoLThreePi (X ⧸ aschbacherSolvableCore 3 X) p e)) →
    aschbacherSolvableCore 3 X = CFSG.pCore 2 X

@[expose] def Gap127TwoCfgPlus : Prop :=
  Gap127TwoCfg ∧
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
      GTwoType129At L K q →
        4 ≤ q.card ∧
        ((∃ hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid, Nonempty (K ⧸ CFSG.pCore 2 K ≃*
          (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) → q.p = 2) ∧
        ∀ hcK : c ∈ K, IsThreeA (QuotientGroup.mk' (CFSG.pCore 2 K) ⟨c, hcK⟩) q.card

end CFSG.RankThree.PartTwo.Sec12
