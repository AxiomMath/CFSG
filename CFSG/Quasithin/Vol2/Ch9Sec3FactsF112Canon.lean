module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112PfB
public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112PfD
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParG2
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Cent
public import CFSG.Sporadic.Schreier.J4SFrattini
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13.Ch9.F112Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
  CFSG.QuasithinUnique.Setup.X6
open scoped commutatorElement

variable {G : Type} [Group G]

theorem f112ListA_cases_canon {L1 L2 S : Subgroup G} (hA : F112ListA L1 L2 S)
    (h1 : IsL2Quot 2 (oTwoQuot ↥L1)) (h2 : IsL2Quot 2 (oTwoQuot ↥L2)) :
    (∃ f, 2 ≤ f ∧ IsAmalgamOfGroup
        (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
        (IsLieOverTwo .PSL 3 f)) ∨
      (∃ f, 2 ≤ f ∧ IsAmalgamOfGroup
        (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) (IsSp4Over f)) ∨
      (∃ f, 2 ≤ f ∧ IsAmalgamOfGroup
        (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) (IsG2Over f)) := by
  unfold F112ListA at hA
  dsimp only at hA
  rcases hA with ⟨f, hf, hα, -⟩ | ⟨f, hf, hα, -⟩ | ⟨f, hf, hα, -⟩ | ⟨f, hf, -, hq, -⟩ |
    ⟨a, -, -, -, -, hq, -⟩ | ⟨f, hf, -, -, -, -, hq, -⟩ | ⟨-, -, -, hq, -⟩
  · exact Or.inl ⟨f, hf, hα⟩
  · exact Or.inr (Or.inl ⟨f, hf, hα⟩)
  · exact Or.inr (Or.inr ⟨f, hf, hα⟩)
  · have := eq_two_of_isL2Quot (by omega) hq h1
    omega
  · have := eq_two_of_isL2Quot (by omega) hq h2
    omega
  · have := eq_two_of_isL2Quot (by omega) hq h2
    omega
  · have := eq_two_of_isL2Quot (by norm_num) hq h2
    omega

theorem f112FourLinkFactC_of (hL3 : ∀ f, 2 ≤ f → HasModelFacts (IsLieOverTwo .PSL 3 f))
    (hSp4 : ∀ f, 2 ≤ f → HasModelFacts (IsSp4Over f))
    (hG2 : ∀ f, 2 ≤ f → HasModelFacts (IsG2Over f)) : F112FourLinkFactC := by
  intro G _ _ L1 L2 S hH hA h1 h2 Li Lj hij Z₀ _ _ _
  have key : pCoreOf 2 (L1 ⊔ S) = ⁅pCoreOf 2 (L1 ⊔ S), L1⁆ ∧
      pCoreOf 2 (L2 ⊔ S) = ⁅pCoreOf 2 (L2 ⊔ S), L2⁆ := by
    rcases f112ListA_cases_canon hA h1 h2 with ⟨f, hf, hα⟩ | ⟨f, hf, hα⟩ | ⟨f, hf, hα⟩
    · exact vertices_of_amalgam hH h1 h2 (hL3 f hf) hα
    · exact vertices_of_amalgam hH h1 h2 (hSp4 f hf) hα
    · exact vertices_of_amalgam hH h1 h2 (hG2 f hf) hα
  rcases hij with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact key.2
  · exact key.1

end CFSG.Quasithin.H13.Ch9.F112Pf

namespace CFSG.Quasithin.H13.Ch9

theorem f112FourLinkFactC_holds :
    F112FourLinkFactC :=
  F112Pf.f112FourLinkFactC_of F112Pf.hasModelFacts_l3 F112Pf.hasModelFacts_sp4
    F112Pf.hasModelFacts_g2

end CFSG.Quasithin.H13.Ch9
