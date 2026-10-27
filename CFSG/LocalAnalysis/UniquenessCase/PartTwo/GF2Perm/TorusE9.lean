module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {K G : Type} [Group K] [Finite K] [Group G] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* G}

theorem exists_E9_le_parJ_singleton (h : BorelQuotient D n H π 3) {F : Type} [Field F]
    {s j : Fin D.rank} (hs : HasTorusSL2 D H s F) (hj : HasOrderThree D j)
    (h6 : Nat.card (rankOne D.rootGroup j) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup j, ∃ b ∈ rankOne D.rootGroup j, a * b ≠ b * a) :
    ∃ E : Subgroup G, E ≤ (parJ D H {j}).map π ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 9 := by
  obtain ⟨φ, hinj, -, -, -, d, b, hdb, hd⟩ := hs
  have hd3 : φ d ^ 3 = 1 := h.torus_pow s _ hd
  obtain ⟨c, hcL, hc1, hc3⟩ := exists_order_three_rankOne hj
  have hcomm : ∀ g ∈ rankOne D.rootGroup j, φ d * g = g * φ d :=
    torus_centralizes_rankOne_of_card_six h h6.1 hd
  obtain ⟨g, hg, hgc⟩ : ∃ g ∈ rankOne D.rootGroup j, g * c ≠ c * g := by
    by_contra hno
    push Not at hno
    exact hc1 (CFSG.AGLEmbeddingD2.McLaughlin.Lie.eq_one_of_central_of_card_six h6.1 h6.2 hcL
      fun x hx => (hno x hx).symm)
  have hdb' : ¬ Commute (φ b) (φ d) := fun hcb => hdb (hinj (by
    rw [map_mul, map_mul]; exact hcb.eq.symm))
  obtain ⟨E, hE, hel, hcard⟩ := exists_E9_le_of_commuting_orders π h.ker_central
    (a₁ := φ d) (a₂ := c) (b₁ := φ b) (b₂ := g) hd3 hc3 (hcomm c hcL)
    (hcomm g hg).symm hgc hdb'
  refine ⟨E, hE.trans (sup_le ?_ ?_), hel, hcard⟩
  · refine Subgroup.zpowers_le.2 ⟨φ d, borel_le_parJ {j} (iSup_le_borel (le_iSup H s hd)), rfl⟩
  · exact Subgroup.zpowers_le.2 ⟨c, rankOne_le_parJ (Set.mem_singleton j) hcL, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
