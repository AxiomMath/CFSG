module

public import CFSG.Quasithin.Background.FFC4Case2
public import CFSG.Quasithin.Background.FFC4Ord3
public import CFSG.Quasithin.Background.B56Inputs

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

@[expose] def B58Case1Good : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ H : Subgroup (MulAut W),
    B53Hyp H → H ≠ ⊥ → ¬ ThreeRank2 ↥H → B56Case1 H → GoodFactor H

section Main

variable {V : Type} [CommGroup V] [Finite V]

namespace B58Split

variable {G A G₁ G₂ F : Subgroup (MulAut V)} (h : B58Split G A G₁ G₂ F)

omit [Finite V] in
include h in
theorem normal_G₁ : (G₁.subgroupOf G).Normal :=
  normal_of_commute (G₁ := G₂) (G₂ := G₁) (by rw [sup_comm]; exact h.sup)
    (fun a ha b hb => (h.comm b hb a ha).symm)

omit [Finite V] in
include h in
theorem conj_mem_G₁ : ∀ g ∈ G, ∀ x ∈ G₁, g * x * g⁻¹ ∈ G₁ := by
  intro g hg x hx
  have := h.normal_G₁.conj_mem ⟨x, h.G₁_le hx⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨g, hg⟩
  simpa [Subgroup.mem_subgroupOf] using this

include h in
theorem case3 (hV : ∀ v : V, v ^ 2 = 1) (h₂ : B56FactorList ↥G₂ ∧ B56Piece G₂ (fixV G₁) (fixV G)) :
    B56Case3 G := by
  obtain ⟨hF₁, hP₁⟩ := h.pieceG₁ hV
  obtain ⟨hF₂, hP₂⟩ := h₂
  have hfixle : fixV G ≤ fixV G₁ := B1.fixV_le_fixV h.G₁_le
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
  · rw [sup_comm, sup_inf_assoc_of_le _ hfixle, h.dec_inf, sup_bot_eq]


include h in
theorem good_of_pair (hq : IsQuotientOfSQTKTauCeti ↥G) (h1 : B58Case1Good) (hV : ∀ v : V, v ^ 2 = 1)
    (hG₂ : G₂ ≠ ⊥) (hb53 : B53Hyp (autSub G₂ (fixV G₁)))
    (hmin : B56Cases (autSub G₂ (fixV G₁))) : GoodFactor (autSub G₂ (fixV G₁)) := by
  have hV₂ : ∀ v : ↥(fixV G₁), v ^ 2 = 1 := fun v => Subtype.ext (hV v)
  have hno : ¬ ThreeRank2 ↥(autSub G₂ (fixV G₁)) := fun hx =>
    h.false_of_threeRank2 hq (hx.of_mulEquiv (resEquiv h.stab h.faithful).symm)
  rcases hmin with hc1 | hc2 | hc3 | hc4 | hc5
  · exact h1 ↥(fixV G₁) hV₂ _ hb53 (h.autSub_ne_bot hG₂) hno hc1
  · exact good_of_case2 hV₂ hc2
  · exact absurd (threeRank2_of_case3 hc3) hno
  · exact absurd (threeRank2_of_case4 hc4) hno
  · exact absurd (threeRank2_of_case5 hc5) hno

end B58Split

theorem asB58_of_case1 (h1 : B58Case1Good) : AsB58 := by
  intro V _ _ G hCE A hA
  by_contra hnot
  have hAne : A ≠ ⊥ := hA.1.2.1
  have hne : ⁅fittingOf G, A⁆ ≠ ⊥ := by
    intro hb
    apply hnot
    rw [Subgroup.commutator_comm] at hb
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hb
  obtain ⟨G₁, G₂, F, hs⟩ := b58_split hCE.hV hCE.hyp.1 hCE.hyp.2.1 hA hne
  have hq := isQuotientOfSQTKTauCeti_of_b53 hCE.hyp
  by_cases hG₂ : G₂ = ⊥
  · exact hCE.not_cases (Or.inr (Or.inl (hs.case2 hCE.hV hG₂)))
  · have hb53 := hs.b53 hCE.hyp.1 hq
    have hV₂ : ∀ v : ↥(fixV G₁), v ^ 2 = 1 := fun v => Subtype.ext (hCE.hV v)
    have hmin := hCE.minimal ↥(fixV G₁) hV₂ (autSub G₂ (fixV G₁)) (hs.autSub_ne_bot hG₂) hb53
      (hs.card_lt hAne)
    have hgood := hs.good_of_pair hq h1 hCE.hV hG₂ hb53 hmin
    exact hCE.not_cases (Or.inr (Or.inr (Or.inl
      (hs.case3 hCE.hV (B58Split.GoodFactor.transport hs hgood)))))

end Main

end FFC

end CFSG.Quasithin
