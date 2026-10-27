module

public import CFSG.Quasithin.Vol2.Ch7Sec77A23Stmts
public import CFSG.Quasithin.H13.KGFact68CSLin
public import CFSG.Quasithin.H13.KGFact68Spor

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Blueprint

@[expose] def TrialityTwoSylowCenterCyclic : Prop :=
  ∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .trialityD4 2 1 →
    ∀ T : Sylow 2 X, IsCyclic (Subgroup.center ↥(T : Subgroup X))

@[expose] def TitsSylowCenterCyclic : Prop :=
  ∀ (X : Type) [Group X] [Finite X], ReeTitsModel X .Tits 2 1 →
    ∀ T : Sylow 2 X, IsCyclic (Subgroup.center ↥(T : Subgroup X))

theorem a23CyclicCenterFact_of (hspor : SporadicSylowCenterCyclic)
    (hD4 : TrialityTwoSylowCenterCyclic) (hTits : TitsSylowCenterCyclic) :
    CFSG.Quasithin.H13.A23CyclicCenterFact := by
  intro S _ _ hS T
  rcases hS with he | ⟨n, hn, h⟩ | h | h | ⟨s, hs, he⟩
  · obtain ⟨e⟩ := he
    exact isCyclic_center_sylow_of_mulEquiv e isCyclic_center_sylow_alt8 T
  · exact isCyclic_center_sylow_of_stated_psl_binary (Or.inr hn) h T
  · exact hD4 S h T
  · exact hTits S h T
  · obtain ⟨e⟩ := he
    exact isCyclic_center_sylow_of_mulEquiv e (hspor s hs) T

end CFSG.Quasithin.H13.KG68
