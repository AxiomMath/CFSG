module

public import CFSG.RankThree.GF2n.Stroth80.Sec78ZtOm4
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaCent

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_QB (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs7 : Sec7Hyp hc n t) :
    ∀ d ∈ Q ⊓ QB B, (∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
      d ∈ Vt M (LB M Q B) B Z t := by
  have hs := hs7.toSec5
  obtain ⟨m, hm, hpm⟩ := hs7.orth
  rcases hpm with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · have hm3 : 3 ≤ m := by
      by_contra hlt
      have : m = 2 := by omega
      subst this
      exact hs7.notPlus4 ⟨K, fK, finK, hK, hnat⟩
    have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
      Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm3, hnat⟩⟩
    haveI : CharP K 2 := sec7ctr_charP hc hK
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
    exact hc.centLam_omega h34 hRoot hs hnatSO hK (ElemMatrixIso.plus hm3)
      (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm3) hnat
  · have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
      Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩
    haveI : CharP K 2 := sec7ctr_charP hc hK
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]; omega
    exact hc.centLam_omega h34 hRoot hs hnatSO hK (ElemMatrixIso.minus hm hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus hm hirr) hnat

end CFSG.RankThree.GF2n.Stroth80
