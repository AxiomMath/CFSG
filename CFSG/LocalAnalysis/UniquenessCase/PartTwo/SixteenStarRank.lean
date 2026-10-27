module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarDef

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16kStar.gamma15_eq_mQuot (hs : S16kStar D V₀ V L hV) :
    gamma15 D.M V₀ V hV L =
      E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) := by
  obtain ⟨ρ, θ, hθ, hequiv, hker, himg⟩ := hs
  let U : Subgroup (Vtil V₀ V hV) := commSub ⊤ (lBar V₀ V hV L)
  let Z : Subgroup (Vtil V₀ V hV) := U ⊓ fixV (lBar V₀ V hV L)
  let f : ↥U →* vStar D.M V₀ V hV L := ρ.comp U.subtype
  have hfker : f.ker = Z.subgroupOf U := by
    ext x
    have hx : (x : Vtil V₀ V hV) ∈ ρ.ker ↔ (x : Vtil V₀ V hV) ∈ Z := by rw [hker]
    change ρ (x : Vtil V₀ V hV) = 1 ↔ x ∈ Z.subgroupOf U
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have hfrange : f.range = wStar D.M V₀ V hV L := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [← himg]
      exact Subgroup.mem_map.mpr ⟨(x : Vtil V₀ V hV), x.2, rfl⟩
    · intro hy
      rw [← himg] at hy
      obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨v, hv⟩, hvy⟩
  have hcard : Nat.card (wStar D.M V₀ V hV L) = Nat.card (U ⧸ Z.subgroupOf U) := by
    have h := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [hfrange, hfker] at h
    exact h.symm
  unfold gamma15 rk
  rw [hcard, ← Subgroup.index_eq_card]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
