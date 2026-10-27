module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.SectionRank

variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']

theorem s15k_table_pRank_le_of_inj {p : ℕ} (hp : 1 < p) {Γ : Subgroup G} (f : ↥Γ →* G')
    (hf : Function.Injective f) {H : Subgroup G} (hH : H ≤ Γ) {H' : Subgroup G'}
    (hfH : ∀ x : ↥Γ, (x : G) ∈ H → f x ∈ H') : pRank p H ≤ pRank p H' := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp H
  have hEΓ : E ≤ Γ := hEH.trans hH
  have hcomm := hE.1
  have hEs : IsElemAbelian p (E.subgroupOf Γ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have h1 := congrArg Subtype.val (mul_comm' (⟨((a : ↥Γ) : G), a.2⟩ : E)
        ⟨((b : ↥Γ) : G), b.2⟩)
      exact h1
    · apply Subtype.ext
      have h1 : ((x : ↥Γ) : G) ^ p = 1 := hE.2 _ hx
      change ((x : ↥Γ) : G) ^ p = 1
      exact h1
  refine le_pRank hp (E := (E.subgroupOf Γ).map f) ?_ (isElemAbelian_map hEs f) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hfH x (hEH hx)
  · rw [Subgroup.card_map_of_injective hf, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
