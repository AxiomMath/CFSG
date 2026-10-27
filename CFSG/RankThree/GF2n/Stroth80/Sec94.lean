module

public import CFSG.RankThree.GF2n.Stroth80.Sec9Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec9_exists_conj_of_not_stronglyClosed {M Z0 L N : Subgroup G}
    (hsc : StronglyClosedMod M Z0 (L ⊓ N)) (hns : ¬ StronglyClosedMod M Z0 L) :
    ∃ s ∈ Z0, ∃ g ∈ M, g * s * g⁻¹ ∈ L ∧ g * s * g⁻¹ ∉ N := by
  unfold StronglyClosedMod at hns
  push_neg at hns
  obtain ⟨s, hs, g, hg, hL, hZ⟩ := hns
  exact ⟨s, hs, g, hg, hL, fun hN => hZ (hsc s hs g hg ⟨hL, hN⟩)⟩

theorem stroth94_of_steps (h93 : Stroth93Statement) (h92 : Stroth92Statement)
    (hB : Step94ConjVStatement) (hN : Step94NSixStatement) (hE : Step94EndStatement) :
    Stroth94Statement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 hsc
  obtain ⟨s, hs0, g, hg, hgL, hgN⟩ :=
    sec9_exists_conj_of_not_stronglyClosed hsc (h93 G M Q Z B hc n t hs Z0 hZ0)
  have hxM : g * s * g⁻¹ ∈ M := hc.LB_le_M hgL
  have hconj : ConjMod M Q s (g * s * g⁻¹) := ⟨hxM, g, hg, by simp [Q.one_mem]⟩
  have hVW := hB G M Q Z B hc n t hs _ _ rfl rfl Z0 hZ0 s hs0 _ hgL hgN hconj
  have hY := (h92 G M Q Z B hc n t hs _ _ rfl rfl _ hgL hgN hVW).1
  exact hE G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 _ hgL hgN hconj hY
    (hN G M Q Z B hc n t hs Z0 hZ0 hsc s hs0 _ hgL hgN hconj hY)

end CFSG.RankThree.GF2n.Stroth80
