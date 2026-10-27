module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPairs
import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
import CFSG.LocalAnalysis.StandardType.GGInndiagThreeAdicInner
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Mark
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLThreeAdic
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

open CFSG.Open in
theorem card_quotient_center_of_D4_marking {X : Type*} [Group X] {n : ℕ}
    (hmark : LargeEvenMarking X fun lab' _ _ _ _ _ => lab' = ⟨.D, 4, n⟩) :
    Nat.card (X ⧸ Subgroup.center X) = ordD 4 (2 ^ n) := by
  obtain ⟨-, l, hl, hraw⟩ := hmark
  obtain ⟨_, _, _, _, -, -, -, rfl⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨R, _, I, F, ⟨-, -, θ, -⟩, hM⟩ := largeEvenRawDatum_exists
    (largeEvenLabelAll_markedModel_classical hl (Or.inr (Or.inr (Or.inr rfl))) _ hraw)
  have hM' : LieModel R .POmegaPlus 4 2 n := by
    have h43 : ¬ ((4 : ℕ) = 3) := by decide
    simpa only [MarkedModel, markTag, markRank, markChar, markDeg, h43, if_false] using hM
  rw [Nat.card_congr θ.toEquiv]
  exact CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hM'

private theorem ggInndiagOnCompAt_of_bound_3k {lab : LargeEvenLabel} (ℓ : ℕ → LargeEvenLabel)
    (o : ℕ → ℕ)
    (hinn : LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R))
    (hdvd : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      Finite R → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ s ∈ I, s ^ p = 1 → s ≠ 1 →
        ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) → ∀ lab' : LargeEvenLabel,
          (lab'.tag = .twD → 3 ≤ lab'.rank) →
          LargeEvenMarking ↥J₁ (fun l _ _ _ _ _ => l = lab') → lab.n ∣ lab'.n)
    (hℓ : ∀ n, (ℓ n).tag ≠ .twD)
    (hbound : LargeEvenLabelAll lab fun R _ _ _ => ∀ n, lab.n ∣ (ℓ n).n → 3 ∣ 2 ^ n + 1 →
      padicValNat 3 (Nat.card R) ≤ padicValNat 3 (o n) + 1)
    (hcard : ∀ {X : Type} [Group X] (n : ℕ),
      LargeEvenMarking X (fun l _ _ _ _ _ => l = ℓ n) → Nat.card (X ⧸ Subgroup.center X) = o n) :
    GGInndiagOnCompAt lab fun n l => l = ℓ n := by
  unfold GGInndiagOnCompAt
  refine (largeEvenLabelAll_and (largeEvenLabelAll_and hinn hdvd) hbound).mono
    fun R _ I _ ⟨⟨hI, hpl⟩, hb⟩ hR hna hfin s t n hs3 hs1 ht3 hst hsI htI hn J₁ hJ₁ hmark => ?_
  haveI := hfin
  have hdn := hpl hR hna hfin 3 Nat.prime_three (by norm_num) s hsI hs3 hs1 J₁ hJ₁ (ℓ n)
    (fun h => absurd h (hℓ n)) hmark
  refine not_ggOutsideInndiag_of_threeAdic (hI hR hna) hR hna hs3 hs1 ht3 hst hsI htI hJ₁ hmark ?_
  rw [hcard n hmark]
  exact hb n hdn hn

theorem ggInndiagOnCompAt_D4_threeAdic {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .F4 ∨ lab.tag = .E6) (h3 : 3 ∣ 2 ^ lab.n + 1) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ := by
  refine ggInndiagOnCompAt_of_bound_3k (fun n => ⟨.D, 4, n⟩) (fun n => CFSG.Open.ordD 4 (2 ^ n))
    ?_ (largeEvenLabelAll_n_dvd_of_isComponentOf_ggFix hlab) (fun _ => by simp) ?_
    fun n hmark => card_quotient_center_of_D4_marking hmark
  · obtain ⟨t, l, g⟩ := lab
    dsimp only at htag h3
    rcases htag with rfl | rfl
    · exact largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inr (Or.inl rfl)))
    · have hl : l = 0 := hlab.2
      subst hl
      exact largeEvenLabelAll_subset_inn_E6_odd (odd_of_three_dvd_two_pow_add_one_noJ1 h3)
  · obtain ⟨t, l, g⟩ := lab
    dsimp only at htag
    rcases htag with rfl | rfl
    · intro Q hQ
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      obtain ⟨K, i1, i2, hK, hq⟩ := hQ
      refine ⟨K, i1, i2, hK, hq, fun n hgn hn => ?_⟩
      exact (congrArg (padicValNat 3)
        (CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4
          (untwistedChevalleyModel_largeEven .F4 hK))).trans_le
        (padicValNat_three_ordF4_le_ordD_four hgn hn)
    · intro Q hQ
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      obtain ⟨K, i1, i2, hK, hq⟩ := hQ
      refine ⟨K, i1, i2, hK, hq, fun n hgn hn => ?_⟩
      exact (congrArg (padicValNat 3)
        (CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_E6
          (untwistedChevalleyModel_largeEven .E6 hK))).trans_le
        (padicValNat_three_ordE6_le_ordD_four hgn hn)

end CFSG.StandardType.SCFourCover

end
