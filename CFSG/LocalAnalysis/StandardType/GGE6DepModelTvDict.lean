module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelActs
public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

variable {G : Type} [Group G] {Bs : Subgroup G}

theorem ggIsTransvection_of_isTv6 {ι : Additive ↥Bs ≃+ Vec6} {φ : MulAut ↥Bs} {g : Mat6}
    (h : ActsAs ι φ g) (hg : IsTv6 g) : GGIsTransvection 3 φ := by
  have hfix : ∀ b : ↥Bs, (φ b = b) ↔ g.mulVec (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
    intro b
    rw [← h b]
    exact ⟨fun hb => by rw [hb], fun hb => Additive.ofMul.injective (ι.injective hb)⟩
  have hcard : Nat.card {b : ↥Bs // φ b = b} = Nat.card {v : Vec6 // g.mulVec v = v} :=
    Nat.card_congr (Equiv.subtypeEquiv (Additive.ofMul.trans ι.toEquiv) hfix)
  have hV : Nat.card {v : Vec6 // g.mulVec v = v} * 3 = 3 ^ 6 := by
    rw [Nat.card_eq_fintype_card]
    exact hg.1
  have hcardBs : Nat.card ↥Bs = 3 ^ 6 := by
    rw [card_eq_of_ggLin ι, Nat.card_fun (α := Fin 6) (β := ZMod 3), Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨?_, ?_⟩
  · rw [hcard, hV, hcardBs]
  · intro b
    apply Additive.ofMul.injective
    apply ι.injective
    have h1 : ι (Additive.ofMul (b⁻¹ * φ b)) =
        g.mulVec (ι (Additive.ofMul b)) - ι (Additive.ofMul b) := by
      rw [ofMul_mul, ofMul_inv, map_add, map_neg, h b]
      abel
    have h2 : ι (Additive.ofMul (φ (b⁻¹ * φ b))) =
        g.mulVec (ι (Additive.ofMul b)) - ι (Additive.ofMul b) := by
      rw [h (b⁻¹ * φ b), h1, hg.2 (ι (Additive.ofMul b))]
    rw [h2, h1]

end E6Dep

end CFSG.StandardType

end
