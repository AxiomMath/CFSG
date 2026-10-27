module

public import CFSG.RankThree.GF2n.Stroth80.Sec310RootSp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix


theorem stroth310Root_of_34 (h34 : Stroth34Statement) : Stroth310RootStatement := by
  intro G _ _ M Q Z B hc n t hs hnat V hV r hr
  subst hV
  have hnatSO := hnat
  rcases hnat with hsp | hom
  · obtain ⟨K, fK, finK, hK, m, hm, φ, hφ, hker, hact⟩ := hsp
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    obtain ⟨-, hn, ψ, hψ⟩ := hact
    haveI := hn
    exact hc.root_sp h34 hs (stroth310NotQB_of_34 h34 G M Q Z B hc n t hs hnatSO) hK hm φ hφ hker ψ
      hψ ⟨r, hr⟩
  · obtain ⟨K, fK, finK, hK, hcase⟩ := hom
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    rcases hcase with ⟨m, hm, hnat'⟩ | ⟨m, b, c, hm, hirr, hnat'⟩
    · haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
      obtain ⟨φ, hφ, hker, hact⟩ := hnat'
      obtain ⟨-, hn, ψ, hψ⟩ := hact
      haveI := hn
      have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
      exact hc.root_omega h34 hs (stroth310NotQB_of_34 h34 G M Q Z B hc n t hs hnatSO) hK
        (ElemMatrixIso.plus hm) (nondegenerate_polarBilin_quadPlus m K) h3
        (addCommutantScalar_statedOmegaPlus hm) φ hφ hker ψ hψ ⟨r, hr⟩
    · haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
      obtain ⟨φ, hφ, hker, hact⟩ := hnat'
      obtain ⟨-, hn, ψ, hψ⟩ := hact
      haveI := hn
      have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
          Fintype.card_fin, Fintype.card_fin]; omega
      exact hc.root_omega h34 hs (stroth310NotQB_of_34 h34 G M Q Z B hc n t hs hnatSO) hK
        (ElemMatrixIso.minus hm hirr) (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
        (addCommutantScalar_statedOmegaMinus hm hirr) φ hφ hker ψ hψ ⟨r, hr⟩

end CFSG.RankThree.GF2n.Stroth80
