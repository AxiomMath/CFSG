module

public import CFSG.Quasithin.Vol2.Ch10SecB3FactsC
public import CFSG.Quasithin.Vol2.Ch10SecASL2OverQ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

theorem factBenderOver_holds : FactBenderOver := by
  intro K _ _ hK S X hS hSX
  rcases hK with ⟨F, _, _, a, ha, hF, ⟨e⟩⟩ | ⟨n, hn⟩
  · exact SecA.le_normalizer_or_eq_top_of_mulEquiv ha hF e hS hSX
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsSimpleGroup K := (CFSG.LieType.Simplicity.fam_2b2_simplicity K 2 n hn).2
    have hB := CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isSz (n := n) hn
    have hidx : ¬ 2 ∣ S.index := by
      have h : ¬ 2 ∣ (S.subgroupOf ⊤).index := hS.2.2
      rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
    by_cases hX : X = ⊤
    · exact Or.inr hX
    · exact Or.inl (CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hB
        (hS.2.1.toSylow hidx) hSX hX)

end CFSG.Quasithin.Vol2.Ch10.SecB
