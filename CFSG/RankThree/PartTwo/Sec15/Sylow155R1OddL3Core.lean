module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1AutDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125Cop
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125W

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem res1AutCent_of_abelian_index_two {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) (hOut : Odd (Nat.card (commutator (Outer S))))
    (hW : ∀ R : Subgroup S, IsPGroup 2 R →
      ∃ A : Subgroup R, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ A.index ≤ 2)
    (hE : ∀ E : Subgroup S, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
      Nat.card E ≤ 4) :
    Res1AutCent S := by
  intro α V y _ hα _ hV hαV _ v hv
  have hαn : α ∈ Subgroup.normalizer (V : Set (MulAut S)) :=
    Subgroup.mem_normalizer_fintype fun n hn => hαV n hn
  exact CFSG.RankThree.PartTwo.Sec15.Sylow155R3.res3L125_centralizes_of_normalizes hZ hOut hW hE
    (fun R _ _ hR A hA hidx hE' β hβ =>
      CFSG.RankThree.PartTwo.Sec15.Sylow155R3.res3L125_eq_one_of_coprime_six hR hA hidx hE' hβ)
    hV hαn hα v hv

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
