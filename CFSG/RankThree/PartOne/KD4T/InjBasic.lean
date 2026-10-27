module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.StandardParabolicCells

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Order

variable {τ : Tag}

theorem eq_of_not_precedes_of_not_precedes_neg {β γ β' γ' : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (hβ' : IsRoot τ β')
    (hγ' : IsRoot τ γ') (eβ : β' = -β) (eγ : γ' = -γ)
    (h1 : ¬Label.Precedes (Sum.inr ⟨β, hβ⟩ : Label τ) (Sum.inr ⟨γ, hγ⟩))
    (h2 : ¬Label.Precedes (Sum.inr ⟨β', hβ'⟩ : Label τ) (Sum.inr ⟨γ', hγ'⟩)) : γ = β := by
  subst eβ eγ
  simp only [Label.Precedes, Label.weight, height_neg, not_or, not_and, not_lt] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have hh : height β = height γ := by omega
  have l1 : toLex γ ≤ toLex β := not_lt.1 (h1b hh)
  have l2 : toLex (-γ) ≤ toLex (-β) := not_lt.1 (h2b (by rw [hh]))
  have l2' : toLex β ≤ toLex γ := neg_le_neg_iff.1 l2
  exact toLex.injective (le_antisymm l1 l2')

variable {K : Type} [Field K]

theorem not_precedes_of_apply_eq_borel
    {n b : ModGL τ K} (hb : b ∈ borelGroup τ K) {w : WeylGroup τ} (hn : MapsRootLines n w)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (h : (n : Module.End K (RootModule τ K)) (rootVec τ K β) =
      (b : Module.End K (RootModule τ K)) (rootVec τ K β)) :
    ¬Label.Precedes (Sum.inr ⟨β, hβ⟩ : Label τ) (Sum.inr ⟨w • β, IsRoot.smul hβ w⟩) := by
  intro hp
  obtain ⟨c, hc⟩ := hn β hβ
  have h0 := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.1 b hb _ _ hp
  rw [← rootVec_eq_single_of_isRoot hβ, ← h, hc, rootVec_eq_single_of_isRoot (IsRoot.smul hβ w),
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h0
  exact c.ne_zero h0

end Order

section Weyl

variable {τ : Tag}

theorem eq_one_of_fix_of_mem_parabolicWeylGroup
    {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ J)
    (h : ∀ j ∈ J, w • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single j 1) : w = 1 := by
  refine eq_one_of_forall_height_pos fun i => ?_
  by_cases hi : i ∈ J
  · rw [h i hi, height_single]
    exact one_pos
  · have hcoord : (w • (Pi.single i 1 : Fin τ.rank → ℤ)) i = 1 := by
      rw [smul_apply_of_mem_parabolicWeylGroup hw _ hi]
      simp
    have hroot := IsRoot.smul (isRoot_single τ i) w
    rcases IsRoot.height_pos_or_neg hroot with hpos | hneg
    · exact hpos
    · exact absurd ((IsRoot.height_neg_iff hroot).1 hneg i) (by rw [hcoord]; norm_num)

end Weyl

end CFSG.RankThree.PartOne.KD4T
