module

public import CFSG.RankThree.GF2n.Stroth80.Sec51Omega
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaSingular

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix


theorem stroth51_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h311a : Stroth311aStatement) (h311bC : Stroth311bCommStatement)
    (h311bK : Stroth311bCardStatement) : Stroth51Statement := by
  intro G _ _ M Q Z B hc n t hs hnat r hr hplane
  rcases hnat with hsp | hom
  · exact sec51_sp h34 hRoot h311a h311bC h311bK G M Q Z B hc n t hs hsp r hr hplane
  · have hnatSO : SpNat hc t ∨ OmegaNat hc t := Or.inr hom
    obtain ⟨K, fK, finK, hK, hcase⟩ := hom
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    rcases hcase with ⟨m, hm, hnat⟩ | ⟨m, b, c, hm, hirr, hnat⟩
    · haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
      have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
      refine sec51_orth h34 hRoot h311a h311bC h311bK hc hs hnatSO hK
        (ElemMatrixIso.plus hm) (nondegenerate_polarBilin_quadPlus m K) h3
        (addCommutantScalar_statedOmegaPlus hm) ?_
        (hc.natSingular_of h34 hRoot hs hnatSO hK (ElemMatrixIso.plus hm)
          (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm))
        hnat r hr hplane
      intro R N P I L₁ L₂ A₁ A₂ φ hφ hNφ hP hI hN hd h₁ h₂ u u' hu hu' huu' hL₁ hL₂
      obtain ⟨n', hn'⟩ := stroth_2_1_ii_secOmegaPlus (ElemMatrixIso.plus hm) hm
        (isPlus_quadPlus m) φ hφ hNφ hP hI hN hd h₁ h₂ hu hu' huu' hL₁ hL₂
      exact ⟨2 ^ (m - 1) * n', (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right n', hn'⟩
    · haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
      have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
          Fintype.card_fin, Fintype.card_fin]; omega
      refine sec51_orth h34 hRoot h311a h311bC h311bK hc hs hnatSO hK
        (ElemMatrixIso.minus hm hirr) (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
        (addCommutantScalar_statedOmegaMinus hm hirr) ?_
        (hc.natSingular_of h34 hRoot hs hnatSO hK (ElemMatrixIso.minus hm hirr)
          (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
          (addCommutantScalar_statedOmegaMinus hm hirr))
        hnat r hr hplane
      intro R N P I L₁ L₂ A₁ A₂ φ hφ hNφ hP hI hN hd h₁ h₂ u u' hu hu' huu' hL₁ hL₂
      obtain ⟨n', hn'⟩ := stroth_2_1_ii_secOmegaMinus (ElemMatrixIso.minus hm hirr) hm
        (isMinus_quadMinus (by omega) hirr) φ hφ hNφ hP hI hN hd h₁ h₂ hu hu' huu' hL₁ hL₂
      exact ⟨2 ^ m * n', (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right n', hn'⟩

end CFSG.RankThree.GF2n.Stroth80
