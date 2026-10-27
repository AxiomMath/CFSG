module

public import CFSG.Quasithin.Background.FFCProdSplitGood
public import CFSG.Quasithin.Background.FFC5Two

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

section Exc

variable {V : Type} [CommGroup V]

namespace B510Data

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Data G G₁ G₂)

include h in
theorem stab : G₂ ≤ stabSub (fixV G₁) :=
  ProdSplit.stab h.comm

include h in
theorem normal : (G₂.subgroupOf G).Normal := normal_of_commute h.sup h.comm

include h in
theorem normal₁ : (G₁.subgroupOf G).Normal :=
  normal_of_commute (G₁ := G₂) (G₂ := G₁) (by rw [sup_comm]; exact h.sup)
    (fun a ha b hb => (h.comm b hb a ha).symm)

include h in
theorem conj_mem_G₁ : ∀ g ∈ G, ∀ x ∈ G₁, g * x * g⁻¹ ∈ G₁ := by
  intro g hg x hx
  have := h.normal₁.conj_mem ⟨x, h.G₁_le hx⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨g, hg⟩
  simpa [Subgroup.mem_subgroupOf] using this

include h in
theorem res_mem : ∀ g ∈ G, ∃ b ∈ G₂, ∀ v ∈ fixV G₁, g v = b v :=
  ProdSplit.res_mem h.sup h.comm

include h in
theorem stab_G : G ≤ stabSub (fixV G₁) :=
  ProdSplit.stab_G h.sup h.comm

include h in
theorem autSub_sup_eq : autSub G (fixV G₁) = autSub G₂ (fixV G₁) :=
  ProdSplit.autSub_sup_eq h.sup h.comm

include h in
theorem ffJ_autSub [Finite V] (hJ : G = ffJ G) :
    autSub G₂ (fixV G₁) ≤ ffJ (autSub G₂ (fixV G₁)) :=
  ProdSplit.ffJ_autSub h.sup h.comm hJ


end B510Data

structure B510Fa (G G₁ G₂ : Subgroup (MulAut V)) : Prop extends B510Data G G₁ G₂ where
  faithful : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1

namespace B510Fa

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Fa G G₁ G₂)

include h in
theorem b53 [Finite V] (hO2 : pCoreOf 2 G = ⊥) (hJ : G = ffJ G) (hq : IsQuotientOfSQTKTauCeti ↥G) :
    B53Hyp (autSub G₂ (fixV G₁)) :=
  ProdSplit.b53 h.sup h.comm h.faithful hO2 hJ hq

include h in
theorem card_lt [Finite V] (hG₁ : G₁ ≠ ⊥) : Nat.card ↥(autSub G₂ (fixV G₁)) < Nat.card ↥G :=
  ProdSplit.card_lt h.sup h.inf h.comm h.faithful hG₁

include h in
theorem autSub_ne_bot (hne : G₂ ≠ ⊥) : autSub G₂ (fixV G₁) ≠ ⊥ :=
  ProdSplit.autSub_ne_bot h.comm h.faithful hne






section Main5

variable [Finite V]

include h in
theorem false_of_threeRank2 (hq : IsQuotientOfSQTKTauCeti ↥G) (hs3 : S3Elems ↥G₁)
    (hX : ThreeRank2 ↥G₂) : False :=
  ProdSplit.false_of_threeRank2 h.G₁_le h.G₂_le h.comm hq hs3 hX

include h in
theorem good
    (hI : B58Inputs) (hc : B56Counterex G) (hG₁ : G₁ ≠ ⊥) (hG₂ : G₂ ≠ ⊥)
    (hs3 : S3Elems ↥G₁) : GoodFactor (autSub G₂ (fixV G₁)) :=
  ProdSplit.good h.sup h.inf h.comm h.faithful hI hc hG₁ hG₂ hs3


end Main5

end B510Fa

end Exc

end FFC

end CFSG.Quasithin
