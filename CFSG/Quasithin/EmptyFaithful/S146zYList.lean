module

public import CFSG.Quasithin.EmptyFaithful.S146zYFacts5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Normal

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.H13.NQCore

@[expose] def QuotientCenterFact : Prop :=
  ∀ {A : Type} [Group A] [Finite A] {L P T : Subgroup A}, E25Config L P T →
    (Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) →
    ∃ (B : Type) (_ : Group B) (_ : Finite B) (L' P' T' : Subgroup B), E25Config L' P' T' ∧
      Nonempty (↥L' ≃* ↥L ⧸ Subgroup.center ↥L) ∧
      (EmptyFaithfulMultiple.AutCyclic T' P' → EmptyFaithfulMultiple.AutCyclic T P)

@[expose] def ComponentListFact : Prop :=
  ∀ {G : Type} [Group G], SQTKHypCat G → ∀ {L : Subgroup G}, CFSG.IsComponent L →
    A23ListCat (↥L ⧸ Subgroup.center ↥L)

@[expose] def CoverL35Fact : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 5 → ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A)
    (Y : Type) [Group Y], SQTKHypCat A → CFSG.IsComponent L →
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* Y) → StatedClassicalModel Y .PSL 3 p 1 →
    Subgroup.center ↥L = ⊥

theorem normal_of_facts5 (hF : Facts134Five) (hQ : QuotientCenterFact)
    (hC : ComponentListFact) (hcov : CoverL35Fact) (h36 : A36CoreForSQTKCat) :
    NormalFiveFact := by
  intro p hp hp5 A _ _ L P T hcfg hcard
  subst hp5
  have hcfg' : E25Config L P T := E25Config.of_oddConfig hcfg (by simpa using hcard)
  have hLc : L ∈ cComp (⊤ : Subgroup A) := mem_cComp_top_of_isComponent hcfg.component
  have hZ := card_center_of_a36Common' hcfg.component.1 ((h36 A hcfg.hyp L hLc).2.1)
  obtain ⟨B, _, _, L', P', T', hcfg2, ⟨e⟩, hlift⟩ := hQ hcfg' hZ
  have hlist : CFSG.Milestones.SQTKSimpleList ↥L' :=
    CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv e (hC hcfg.hyp hcfg.component)
  rcases hlist with ⟨n, hn5, hn8, ⟨e'⟩⟩ | ⟨q, hq, hq2, hodd⟩ | (⟨f, hf⟩ | hf) | ⟨n, hn, hmod⟩ |
    ⟨s, hs, ⟨e'⟩⟩
  ·
    exact (hF.alt B L' P' T' ⟨n, hn5, hn8, ⟨e'⟩⟩ hcfg2).elim
  ·
    rcases hodd with ⟨f, hf, hmod⟩ | hmod | hmod
    · exact (hF.psl2Odd q f hq hq2 hf B L' P' T' hmod hcfg2).elim
    · by_cases hq5 : q = 5
      ·
        subst hq5
        have hZ1 : Subgroup.center ↥L = ⊥ :=
          hcov 5 rfl A L ↥L' hcfg.hyp hcfg.component ⟨e.symm⟩ hmod
        let e0 : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
          QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ1.symm)
        exact Or.inl (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv (e0.trans e.symm)
          hmod))
      · exact (hF.psl3Odd q hq hq2 hq5 B L' P' T' hmod hcfg2).elim
    · exact (hF.psu3Odd q hq hq2 B L' P' T' hmod hcfg2).elim
  ·
    rcases hf with ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ | ⟨-, hmod⟩ |
      ⟨-, -, hmod⟩ | ⟨-, -, hmod⟩
    · exact (hF.psl2Even f B L' P' T' hmod hcfg2).elim
    · exact (hF.psl3Even f B L' P' T' hmod hcfg2).elim
    · exact (hF.psu3Even f B L' P' T' hmod hcfg2).elim
    · exact Or.inr (hlift (hF.psp4Even f B L' P' T' hmod hcfg2))
    · exact (hF.g2Even f B L' P' T' hmod hcfg2).elim
    · exact (hF.d4Even f B L' P' T' hmod hcfg2).elim
    · exact (hF.f4Even f B L' P' T' hmod hcfg2).elim
    · exact (hF.sz f B L' P' T' hmod hcfg2).elim
  ·
    exact (hF.tits B L' P' T' hf hcfg2).elim
  ·
    exact (hF.psl45 n hn B L' P' T' hmod hcfg2).elim
  ·
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hF.m11 B L' P' T' ⟨e'⟩ hcfg2).elim
    · exact (hF.m12 B L' P' T' ⟨e'⟩ hcfg2).elim
    · exact (hF.m22 B L' P' T' ⟨e'⟩ hcfg2).elim
    · exact (hF.m23 B L' P' T' ⟨e'⟩ hcfg2).elim
    · exact (hF.m24 B L' P' T' ⟨e'⟩ hcfg2).elim
    · exact (hF.j1 B L' P' T' ⟨e'⟩ hcfg2).elim
    · exact (hF.j2 B L' P' T' ⟨e'⟩ hcfg2).elim
    · exact (hF.j4 B L' P' T' ⟨e'⟩ hcfg2).elim
    · exact (hF.hs B L' P' T' ⟨e'⟩ hcfg2).elim
    · exact (hF.he B L' P' T' ⟨e'⟩ hcfg2).elim
    · exact (hF.ru B L' P' T' ⟨e'⟩ hcfg2).elim

end CFSG.Quasithin.S146zY
