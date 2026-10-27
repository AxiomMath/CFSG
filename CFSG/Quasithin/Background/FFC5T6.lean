module

public import CFSG.Quasithin.Background.FFC5T1
public import CFSG.Quasithin.Background.FFC5T2

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section T7

variable {V : Type} [CommGroup V]

theorem commV_invariant_coe (X : Subgroup (MulAut V)) :
    ∀ g : ↥X, ∀ u ∈ commV X, (g : MulAut V) u ∈ commV X :=
  fun g u hu => commV_invariant_self X g g.2 u hu

namespace B510Fa

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Fa G G₁ G₂)

include h in
theorem commV_inf_fixV_eq : fixV G₂ ⊓ commV G₂ = fixV G ⊓ commV G₂ := by
  have h1 : fixV G = fixV G₁ ⊓ fixV G₂ := h.fixV_eq
  rw [h1]
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨⟨h.commV_le hx2, hx1⟩, hx2⟩
  · rintro ⟨⟨-, hx1⟩, hx2⟩
    exact ⟨hx1, hx2⟩

include h in
theorem case5_sl2 [Finite V] (hnat : BinaryNaturalSL G₁ (commV G₁) ⊥ 3 1)
    (hidx : (commV G₁ ⊔ fixV G₁).index = 2) (hV₂ : fixV G₁ = commV G₂ ⊔ fixV G) {n : ℕ}
    (hn : BinaryNaturalSL G₂ (fixV G₁) (fixV G) 2 n) : B56Case5 G := by
  refine h.case5_of hnat hidx hV₂ (Or.inr ⟨n, ?_⟩)
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
  have hres := realizesVia_restrict hπ (U' := commV G₂) hV₂.symm (commV_invariant_coe G₂)
  rw [← commV_inf_fixV_eq h, inf_comm] at hres
  exact ⟨K, hK, hf, hc, π, by rwa [inf_comm] at hres⟩

end B510Fa

end T7

end FFC

end CFSG.Quasithin
