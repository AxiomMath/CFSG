module

public import CFSG.Quasithin.H13.NQCatExceptional
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs

public section

namespace CFSG.Quasithin.H13.OutTwoNilp

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)

theorem twoNilpotent_outer_of_G2
    {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel S .G2 2 f) : TwoNilpotent (Outer S) := by
  have := NQCat.outer_isCyclic_of_even_G2_model hf h
  exact twoNilpotent_of_isCyclic

theorem twoNilpotent_outer_of_trialityD4
    {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel S .trialityD4 2 f) : TwoNilpotent (Outer S) := by
  have := NQCat.outer_isCyclic_of_even_trialityD4_model hf h
  exact twoNilpotent_of_isCyclic

theorem twoNilpotent_outer_of_twistedF4
    {S : Type} [Group S] [Finite S] {f : ℕ} (h : ReeTitsModel S .twistedF4 2 f) :
    TwoNilpotent (Outer S) := by
  have := (large_Ree_model_field_outer_group_and_inner_involutions S 2 f h).2.2.2.1
  exact twoNilpotent_of_isCyclic

theorem twoNilpotent_outer_of_suzuki
    {S : Type} [Group S] [Finite S] {f : ℕ} (h : SuzukiModel S 2 f) : TwoNilpotent (Outer S) := by
  have := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S 2 f h).1.1
  exact twoNilpotent_of_isCyclic

theorem twoNilpotent_outer_of_tits
    {S : Type} [Group S] (h : ReeTitsModel S .Tits 2 1) : TwoNilpotent (Outer S) :=
  twoNilpotent_of_isPGroup_two (Sporadic.Schreier.Tits.AT_Tits_model_Schreier S 2 1 h).1

end CFSG.Quasithin.H13.OutTwoNilp
