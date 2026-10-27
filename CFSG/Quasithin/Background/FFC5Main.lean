module

public import CFSG.Quasithin.Background.FFCProdSplitGood
public import CFSG.Quasithin.Background.FFC5Res

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

section Main5

variable {V : Type} [CommGroup V] [Finite V]

namespace B511Split

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B511Split G G₁ G₂)

include h in
theorem false_of_threeRank2 (hq : IsQuotientOfSQTKTauCeti ↥G) (hs3 : S3Elems ↥G₁)
    (hX : ThreeRank2 ↥G₂) : False :=
  ProdSplit.false_of_threeRank2 h.G₁_le h.G₂_le h.comm hq hs3 hX

include h in
theorem good
    (hI : B58Inputs) (hc : B56Counterex G) (hG₁ : G₁ ≠ ⊥) (hG₂ : G₂ ≠ ⊥)
    (hs3 : S3Elems ↥G₁) : GoodFactor (autSub G₂ (fixV G₁)) :=
  ProdSplit.good h.sup h.inf h.comm h.faithful hI hc hG₁ hG₂ hs3

omit [Finite V] in
include h in
theorem case3 (h₁ : B56FactorList ↥G₁ ∧ B56Piece G₁ (commV G₁ ⊔ fixV G) (fixV G))
    (h₂ : B56FactorList ↥G₂ ∧ B56Piece G₂ (fixV G₁) (fixV G)) : B56Case3 G := by
  obtain ⟨hF₁, hP₁⟩ := h₁
  obtain ⟨hF₂, hP₂⟩ := h₂
  have hfixle : fixV G ≤ fixV G₁ := B1.fixV_le_fixV h.G₁_le
  have hfixG : fixV G = fixV G₁ ⊓ fixV G₂ := by rw [← h.sup, fixV_sup]
  have hV₁V₂ : commV G₁ ⊓ fixV G₁ ≤ fixV G := by
    intro x hx
    rw [hfixG]
    exact ⟨hx.2, fun b hb => h.triv₁ b hb x hx.1⟩
  refine ⟨G₁, G₂, h.sup, h.inf, h.comm, hF₁, hF₂, commV G₁ ⊔ fixV G, fixV G₁, le_sup_right,
    hfixle, ?_, ?_, ?_, ?_, hP₁, hP₂⟩
  · intro a l hl
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hl
    show (a : MulAut V) (y * z) ∈ commV G₁ ⊔ fixV G
    rw [map_mul]
    refine Subgroup.mul_mem_sup ?_ ?_
    · exact commV_invariant (fun x hx => h.conj_mem_G₁ _ a.2 x hx) hy
    · rw [hz a a.2]; exact hz
  · intro a l hl
    show (a : MulAut V) l ∈ fixV G₁
    refine fixV_invariant (fun x hx => ?_) hl
    have := h.conj_mem_G₁ (a : MulAut V)⁻¹ (G.inv_mem a.2) x hx
    simpa using this
  · rw [sup_assoc, sup_eq_right.2 hfixle]
    exact h.dec_sup
  · rw [sup_comm, sup_inf_assoc_of_le _ hfixle]
    exact le_antisymm (sup_le le_rfl (inf_comm (commV G₁) (fixV G₁) ▸ hV₁V₂)) le_sup_left

include h in
theorem false_of_split
    (hI : B58Inputs) (hc : B56Counterex G) (hG₁ : G₁ ≠ ⊥) (hG₂ : G₂ ≠ ⊥)
    (hs3 : S3Elems ↥G₁) (h₁ : B56FactorList ↥G₁ ∧ B56Piece G₁ (commV G₁ ⊔ fixV G) (fixV G)) : False :=
  hc.not_cases (Or.inr (Or.inr (Or.inl (h.case3 h₁ (B511Split.GoodFactor.transport h
    (h.good hI hc hG₁ hG₂ hs3))))))

end B511Split

end Main5

end FFC

end CFSG.Quasithin
