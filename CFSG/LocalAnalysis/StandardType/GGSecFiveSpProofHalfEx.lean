module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofHalf
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLift

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal Matrix

section Data

theorem ggSecFiveDataInputRest_of_cases_halfAutEx (hNW : GGSecFiveNonWeylInput)
    (hE : GGTypeAJoinEndNodeInput) (hC : GGTypeACorankTwoExInput)
    (hH : GGTypeAHalfEndNodesAutInput) (hHL : GGTypeAHalfLargeAutInput)
    (hA : GGSecFiveWeylAInput) (hB : GGSecFiveWeylBInput) (hD : GGSecFiveWeylDInput)
    (hEx : GGSecFiveWeylEInput) (hF : GGSecFiveWeylF4Input) (hG : GGSecFiveWeylG2Input) :
    GGSecFiveDataInputRest := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNoTr hW hnA
  have hR : GGSecFiveRestHyp p B Bs x L D J := ⟨hcfg, hOp, hInn, hNoTr, hW, hnA⟩
  show GGSecFiveData p B x L D J
  by_cases hWC : GGSecFiveWeylCase' p B Bs x D J
  swap
  · exact hNW G p B Bs x L D J hR hWC
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
  by_cases hHalf : ∃ (n : ℕ) (y : G) (K : Subgroup G), GGTypeAHalfNbr p B Bs x L D J n y K
  · obtain ⟨n, y, K, hN⟩ := hHalf
    have hn : 5 ≤ n := hN.2.2.1
    by_cases hAut : GGHalfAutWithin Bs L K
    · exact Or.inl ⟨n + 1 + 1, n + 1, 1, by omega, by omega, le_rfl,
        ggSecFiveTypeA_of_halfAut hH hcfg hOp hInn hNoTr hN hAut⟩
    · exact hHL G p B Bs x L D J n y K hR hWC hTA hN hAut
  · by_cases hAll : GGSecFiveAllAJoin p B Bs x L D J
    · obtain ⟨y, K, hnbr⟩ := exists_ggNbr hcfg.1.2.2.2.2.2.2.2 hcfg.2.2
      obtain ⟨n, hn, hT⟩ := hAll y K hnbr
      exact hA G p B Bs x L D J hR hWC ⟨n, hn, y, K, hnbr, hT⟩ hTA
    · rcases hR.exists_nonA_weylAt hWC hAll with hBt | hDt | hE6 | hE7 | hE8 | hFt | hGt
      · exact hB G p B Bs x L D J hR hWC hBt hHalf
      · exact hD G p B Bs x L D J hR hWC hDt
      · exact hEx G p B Bs x L D J hR hWC (Or.inl hE6)
      · exact hEx G p B Bs x L D J hR hWC (Or.inr (Or.inl hE7))
      · exact hEx G p B Bs x L D J hR hWC (Or.inr (Or.inr hE8))
      · exact hF G p B Bs x L D J hR hWC hFt
      · exact hG G p B Bs x L D J hR hWC hGt

theorem ggSecFiveDataInputRest_of_rest4_halfAutEx (hNW : GGSecFiveNonWeylInput)
    (hE : GGTypeAJoinEndNodeInput) (hC : GGTypeACorankTwoExInput)
    (hH : GGTypeAHalfEndNodesAutInput) (hHL : GGTypeAHalfLargeAutInput) (hL : GGSpLiftInput)
    (hSE : GGSpJoinEndNodeInput) (hSJ : GGSpJoinInput) (h : GGSecFiveWeylRest4) :
    GGSecFiveDataInputRest :=
  ggSecFiveDataInputRest_of_cases_halfAutEx hNW hE hC hH hHL h.1
    (ggSecFiveWeylBInput_of_typeC hL hSE hSJ h.2.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

end Data

section Compat

theorem ggCompatNbrSomeInput_of_secFive_halfAutEx (hc₃ : GGNoTransvectionInput)
    (hd : GGCoxeterLabelInput) (hA : GGTypeAEndNodeInput) (hE : GGTypeAJoinEndNodeInput)
    (hC : GGTypeACorankTwoExInput) (hH : GGTypeAHalfEndNodesAutInput)
    (hHL : GGSecFiveCompatHalfLargeInput) (hSpL : GGSpLiftInput) (hSpE : GGSpJoinEndNodeInput)
    (hSpJ : GGSpJoinInput) (hrest : GGSecFiveCompatRestInput) : GGCompatNbrSomeInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn t n f ψ hpres
  have hNoTr := hc₃ G p B Bs x L D J hcfg hOp hInn
  have hW := hd G p B Bs x L D J hcfg hOp hInn hNoTr
  by_cases hlevi : GGSecFiveLeviCase p B Bs x L D J
  · rcases hlevi with ⟨m, f', y, K, hN⟩ | ⟨m, y, K, hN⟩ | ⟨m, f', y, K, hN⟩
    · by_cases hsplit : ∃ n' f'' : ℕ, GGTypeASplitConfig p B Bs x L D J n' f''
      · obtain ⟨n', f'', hS⟩ := hsplit
        exact ggSecFiveCompat_of_endNodeInput hA hcfg hOp hInn hNoTr hS
      have hdiv : p ∣ m + 3 := by
        by_contra hp
        exact hsplit ⟨m, f', hN.splitConfig hp⟩
      by_cases hjoin : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K
      · exact ggSecFiveCompat_of_join hE hcfg hOp hInn hNoTr hN hjoin
      · push Not at hjoin
        exact ggSecFiveCompat_of_corankTwoEx hC hcfg hOp hInn hNoTr hN hdiv hjoin
    · by_cases hAut : GGHalfAutWithin Bs L K
      · exact ggSecFiveCompat_of_halfAut hH hcfg hOp hInn hNoTr hN hAut
      · exact hHL G p B Bs x L D J hcfg hOp hInn hNoTr hW t n f ψ hpres m y K hN hAut
    · exact ggSecFiveCompat_of_typeC hSpL hSpE hSpJ hcfg hOp hInn hNoTr hN
  · exact hrest G p B Bs x L D J hcfg hOp hInn hNoTr hW t n f ψ hpres hlevi

end Compat

end CFSG.StandardType
