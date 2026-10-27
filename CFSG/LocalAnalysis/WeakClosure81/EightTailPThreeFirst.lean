module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpU
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSym

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

theorem rankBarV_eq_one_of_oddQuot (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H) {V H T : Subgroup G}
    (hV : Hyp7 V) (hH : IsCalH V H) (hH0 : ¬ IsCalH0 V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))) (hKT : H = kGenIn V H ⊔ T)
    {m : ℕ} (hm : 3 < m) (h3 : KBarOddQuotShape V H T (fun X _ => IsSymGp X m)) :
    rankBarV V H T = 1 := by
  obtain ⟨X, _, _, φ, d, -⟩ := exists_shapeData h711 hV hH hH0 hT hKT
  have h2 := card_barSub_eq_two_of_symGp h711 d hm (isSymGp_of_kBarOddQuotShape d h3)
  have h1 := d.hyp83.card_barSub_eq_two_pow_rankBarV d.eq_sup d.bar
  rw [h2] at h1
  exact Nat.pow_right_injective le_rfl (h1.symm.trans (pow_one 2).symm)

section Certified


theorem w3Lem85ThreeFirst'_holds (hLie : SpPSULieFacts) (hRU : UnitaryRootCommutatorRank)
    (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H) (g4 : W3Lem85TwoGap4) (g6 : W3Lem85TwoGap6)
    (hTwo : W3Lem85TwoKT G) : W3Lem85ThreeFirst' G := by
  intro V H T hV hH hH0 hT hKT hyp
  rcases hyp with h1 | h2 | ⟨m, hm, hOdd⟩
  · exact threeFirst_spu hLie hRU h711 g4 g6 V H T hV hH hH0 hT hKT (Or.inl h1)
  · exact threeFirst_spu hLie hRU h711 g4 g6 V H T hV hH hH0 hT hKT (Or.inr h2)
  · by_cases hSp4 : KBarCenterShape V H T (fun X _ => IsSpGp X 4 1)
    · exact threeFirst_spu hLie hRU h711 g4 g6 V H T hV hH hH0 hT hKT
        (Or.inl ⟨4, 1, by norm_num, hSp4, rankBarV_eq_one_of_oddQuot h711 hV hH hH0 hT hKT hm hOdd⟩)
    · exact threeFirst_symmetric h711 hTwo V H T hV hH hH0 hT hKT ⟨m, hm, hOdd⟩ hSp4

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
