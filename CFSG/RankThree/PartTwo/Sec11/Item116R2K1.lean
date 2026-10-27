module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1CensusPure
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.OutThreeCore

public section

open CFSG CFSG.RankThree.PartTwo Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem pRank_three_top_le_one_of_cyclic_sylow {J : Type} [Group J] [Finite J]
    (hcyc : ∀ P : Sylow 3 J, IsCyclic ↥(P : Subgroup J)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup J) ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc' : ∀ X : Subgroup J, IsPGroup 3 X → IsCyclic ↥X := by
    intro X hX
    obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
    haveI := hcyc Q
    exact isCyclic_of_injective (Subgroup.inclusion hXQ) (Subgroup.inclusion_injective hXQ)
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, -, ⟨hEc, hE3⟩, hEk⟩
  by_contra hk
  push Not at hk
  have hEk' : Nat.card E = 3 ^ k := hEk
  have hEp : IsPGroup 3 E := IsPGroup.of_card hEk'
  haveI := hcyc' E hEp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
  have hg3 : g ^ 3 = 1 := Subtype.ext (hE3 g g.2)
  have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : Nat.card E ∣ 3 := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hg3
  rw [hEk'] at hdvd
  have h2 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
  have h9 : 9 ∣ 3 := by
    have := h2.trans hdvd
    simpa using this
  omega

section Certified


theorem cyclicSylowThreeOutAbelian_holds
    : CyclicSylowThreeOutAbelian := by
  intro J _ _ hKG hsimple hnonab hcyc σ τ
  haveI := hsimple
  have hcat : CFSG.Open.IsCatalogGroup J :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.isCatalogGroup_of_isKGroup_simple hKG
  exact CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.outCommInner_of_catalog hsimple hnonab
    hcat (pRank_three_top_le_one_of_cyclic_sylow hcyc) σ τ

end Certified

end CFSG.RankThree.PartTwo.Sec11
