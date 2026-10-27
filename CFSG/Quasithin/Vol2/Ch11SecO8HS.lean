module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def FactCCompTorus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S J A D : Subgroup G),
    CFSG.SectionRank.IsSQTKCat ↥H → QuasithinUnique.IsSylowTwoOf S H → J ∈ cComp H →
    CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → CFSG.pRank 3 ↥J ≤ 1 →
    Nat.Coprime (Nat.card A) (2 * Nat.card J) →
    (∀ s ∈ S, A ≤ Subgroup.normalizer (CFSG.conjugate J s : Set G)) →
    QuasithinUnique.Lin2.IsHallTwoPrimeOf D
      (conjClosure J S ⊓ Subgroup.normalizer (S : Set G)) →
    (∃ g ∈ conjClosure J S,
      A ≤ Subgroup.centralizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) →
      ⁅J, A⁆ ≤ pCoreOf 2 J

end CFSG.Quasithin.Vol2.Ch11.SecD
