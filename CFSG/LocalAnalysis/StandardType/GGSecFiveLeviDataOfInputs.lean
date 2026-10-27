module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofHalfEx
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylB

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Levi

theorem ggSecFiveLeviData_of_inputs (hE : GGTypeAJoinEndNodeInput)
    (hC : GGTypeACorankTwoExInput) (hH : GGTypeAHalfEndNodesAutInput)
    (hHL : GGTypeAHalfLargeAutInput) (hL : GGSpLiftInput) (hSE : GGSpJoinEndNodeInput)
    (hSJ : GGSpJoinInput) : GGSecFiveLeviData := by
  intro G _ _ p B Bs x L D J hR hWC hLevi
  have hcfg : GGConfig p B Bs x L D J := hR.1
  have hOp : GGOpAutTrivial p Bs := hR.2.1
  have hInn : GGInnerDiagAll p B Bs x L D J := hR.2.2.1
  have hNoTr : GGNoTransvection p Bs := hR.2.2.2.1
  by_cases hTA : ∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbr p B Bs x L D J n f y K
  · obtain ⟨n, f, y, K, hN⟩ := hTA
    have hf1 : 1 ≤ f := hN.1.1.2.1
    have hn : 3 ≤ n := hN.2.2.1
    by_cases hjoin : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K
    · exact Or.inl ⟨n + 1, n + 1, f, by omega, le_rfl, hf1,
        ggSecFiveTypeA_of_join hE hcfg hOp hInn hNoTr hN hjoin⟩
    · push Not at hjoin
      exact Or.inl ⟨n + 1 + 1, n + 1, f, by omega, by omega, hf1,
        ggSecFiveTypeA_of_corankTwoEx hC hcfg hOp hInn hNoTr hN (hR.dvd_of_typeANbr hN) hjoin⟩
  ·
    rcases hLevi with ⟨n, f, y, K, hN⟩ | ⟨n, y, K, hN⟩ | ⟨n, f, y, K, hN⟩
    · exact absurd ⟨n, f, y, K, hN⟩ hTA
    ·
      have hn : 5 ≤ n := hN.2.2.1
      by_cases hAut : GGHalfAutWithin Bs L K
      · exact Or.inl ⟨n + 1 + 1, n + 1, 1, by omega, by omega, le_rfl,
          ggSecFiveTypeA_of_halfAut hH hcfg hOp hInn hNoTr hN hAut⟩
      · exact hHL G p B Bs x L D J n y K hR hWC hTA hN hAut
    ·
      have hf : 1 ≤ f := hN.1.1.2.1
      have hperf : commutator L = ⊤ := hcfg.1.2.2.2.2.2.2.2.1.1
      obtain ⟨φ₁, hφ, hφL⟩ := hL G L n f hN.2.1 hperf hN.1
      obtain ⟨T, hTLK, hT, hKle⟩ :=
        hSE G p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN φ₁ hφ hφL
      have hTG : T ∈ ggG0 p B x L D J :=
        (sup_le (le_ggG0_left p B x L D J) (le_ggG0_of_ggNbr hN.2.2.2.1)) hTLK
      exact Or.inr (Or.inl ⟨.PSp, n + 1, f,
        ggSecFiveLocal_of_spEndNode hN.2.1 hf φ₁ hφ hφL hT hTG
          (fun y' K' hK' =>
            (hSJ G p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN y' K' hK').trans
              (sup_le le_sup_left hKle))⟩)

end Levi

end CFSG.StandardType

end
