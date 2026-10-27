module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPairs
import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
import CFSG.LocalAnalysis.StandardType.GGInndiagThreeAdicInner
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLThreeAdic
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLThreeAdicCells
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1MarkTriality
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Ppd
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDetOrders

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open TableB

private theorem ordA_two_facts_linTwo {r : ℕ} (hr : r ≤ 8) :
    0 < ordA r 2 ∧ ¬ 3 ^ 6 ∣ ordA r 2 := by
  interval_cases r <;> exact ⟨by decide +kernel, by decide +kernel⟩

private theorem padicValNat_three_ordA_two_le_linTwo {r : ℕ} (hr : r ≤ 8) :
    padicValNat 3 (ordA r 2) ≤ 5 := by
  obtain ⟨h0, h6⟩ := ordA_two_facts_linTwo hr
  by_contra h
  exact h6 ((padicValNat_dvd_iff_le_of_ne_one (by norm_num) h0.ne').2 (by omega))

private theorem not_ordTrialityD4_dvd_ordA_linTwo {r n : ℕ} (hr1 : 1 ≤ r) (hr : r + 1 ≤ 9)
    (hn : 1 ≤ n) : ¬ ordTrialityD4 (2 ^ n) ∣ ordA r 2 := by
  intro hd
  obtain ⟨p, hp, hpd⟩ := exists_ppd_dvd_ordTrialityD4 hn (Or.inr (Or.inr rfl)) (by omega)
  have hpA : p ∣ ordA r (2 ^ 1) := by rw [pow_one]; exact hpd.trans hd
  obtain ⟨i, hi, hdvd⟩ := ((CFSG.SeitzReduction.F4Pilot.profile_idxA (n := r) (f := 1) hr1
    le_rfl).prim p (12 * n) hp (by omega)).1 hpA
  rw [Finset.mem_Icc] at hi
  have := Nat.le_of_dvd (by omega) hdvd
  omega

private theorem largeEvenLabelAll_card_A_linTwo {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .A) :
    LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = ordA lab.rank (2 ^ lab.n) := by
  refine fun Q hQ => largeEvenRawDatum_mono (fun R _ _ _ hq => ⟨hq.1, ?_⟩)
    (largeEvenLabelAll_markedModel_classical hlab (Or.inl htag) Q hQ)
  obtain ⟨t, l, g⟩ := lab
  dsimp only at htag ⊢
  subst htag
  exact CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
    (show LieModel R .PSL (l + 1) 2 g from hq.2)

private theorem largeEvenLabelAll_card_D_three_linTwo {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .D) (hr : lab.rank = 3) :
    LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = ordA 3 (2 ^ lab.n) := by
  refine fun Q hQ => largeEvenRawDatum_mono (fun R _ _ _ hq => ⟨hq.1, ?_⟩)
    (largeEvenLabelAll_markedModel_classical hlab (Or.inr (Or.inr (Or.inr htag))) Q hQ)
  obtain ⟨t, l, g⟩ := lab
  dsimp only at htag hr ⊢
  subst htag hr
  exact CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
    (show LieModel R .PSL 4 2 g from hq.2)

private theorem ggInnerDiagInnLabel_A_linTwo {lab : LargeEvenLabel} (htag : lab.tag = .A)
    (hn : lab.n = 1) : GGInnerDiagInnLabel lab :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨htag, by rw [hn]; exact Nat.coprime_one_left _⟩)))))))


private theorem ggInndiagOnCompAt_A_two_triD4 {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .A) (hn : lab.n = 1)
    (hr : lab.rank + 1 ≤ 9) : GGInndiagOnCompAt lab fun n l => l = ⟨.triD4, 0, n⟩ := by
  have hr1 : 1 ≤ lab.rank := by
    have h := hlab.2
    rw [htag] at h
    exact h.1
  refine ggInndiagOnCompAt_of_noJ1 hlab (fun n => n) (fun _ _ h => by subst h; exact ⟨by simp, rfl⟩)
    (largeEvenLabelAll_noJ1_triD4_of_card (largeEvenLabelAll_card_A_linTwo hlab htag)
      (by rw [hn, pow_one]; exact (ordA_two_facts_linTwo (by omega)).1)
      fun n hn1 _ _ => Or.inl ?_)
  rw [hn, pow_one]
  exact not_ordTrialityD4_dvd_ordA_linTwo hr1 hr hn1

theorem ggInndiagOnCompAt_A_two_dPair {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A) (hn : lab.n = 1) (hr : lab.rank + 1 ≤ 9) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩ := by
  refine ggInndiagOnCompAt_or (P := fun n l => l = ⟨.D, 4, n⟩) ?_
    (ggInndiagOnCompAt_A_two_triD4 hlab htag hn hr)
  unfold GGInndiagOnCompAt
  refine (largeEvenLabelAll_and
    (largeEvenLabelAll_subset_inn hlab (ggInnerDiagInnLabel_A_linTwo htag hn))
    (largeEvenLabelAll_card_A_linTwo hlab htag)).mono
    fun R _ I _ ⟨hI, hc⟩ hR hna hfin s t n hs3 hs1 ht3 hst hsI htI hn3 J₁ hJ₁ hmark => ?_
  haveI := hfin
  refine not_ggOutsideInndiag_of_threeAdic (hI hR hna) hR hna hs3 hs1 ht3 hst hsI htI hJ₁ hmark ?_
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at hn3
  have h1 : 1 ≤ padicValNat 3 (2 ^ n + 1) :=
    @one_le_padicValNat_of_dvd 3 _ ⟨Nat.prime_three⟩ (by positivity) hn3
  rw [card_quotient_center_of_D4_marking hmark, hc, hn, pow_one,
    padicValNat_three_ordD_four ((Nat.even_pow' hn0).2 even_two) (Nat.le_self_pow hn0 2) hn3]
  have := padicValNat_three_ordA_two_le_linTwo (r := lab.rank) (by omega)
  omega

theorem ggInndiagOnCompAt_D_three_two_dPair {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .D) (hr : lab.rank = 3) (hn : lab.n = 1) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩ :=
  ggInndiagOnCompAt_of_noJ1 hlab (fun n => n)
    (fun _ _ h => by rcases h with rfl | rfl <;> exact ⟨by simp, rfl⟩)
    (largeEvenLabelAll_noJ1_dPair_of_card (largeEvenLabelAll_card_D_three_linTwo hlab htag hr)
      (by rw [hn]; decide +kernel)
      (fun n hn1 _ _ => Or.inr (by
        rw [hn]
        exact le_trans (by decide +kernel) (ordD_four_two_pow_le hn1 (one_dvd n))))
      (fun n hn1 _ _ => Or.inr (by
        rw [hn]
        exact le_trans (by decide +kernel) (ordTrialityD4_two_pow_le hn1 (one_dvd n)))))

theorem ggInndiagOnCompAt_D_three_two_aPair {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .D) (hr : lab.rank = 3) (hn : lab.n = 1) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩ :=
  ggInndiagOnCompAt_of_noJ1 hlab (fun n => 3 * n)
    (fun _ _ h => by rcases h with rfl | rfl <;> exact ⟨by simp, rfl⟩)
    (largeEvenLabelAll_noJ1_aPair_of_card (largeEvenLabelAll_card_D_three_linTwo hlab htag hr)
      (by rw [hn]; decide +kernel)
      (fun n _ hodd _ => Or.inr (by
        rw [hn]
        exact le_trans (by decide +kernel) (ordA_two_two_pow_le (g := 3) (by decide)
          (Nat.odd_mul.2 ⟨by decide, hodd⟩) (dvd_mul_right 3 n))))
      (fun n _ hodd _ => Or.inr (by
        rw [hn]
        exact le_trans (by decide +kernel) (ordTwistedA_two_two_pow_le (g := 3) (by decide)
          (Nat.odd_mul.2 ⟨by decide, hodd⟩) (dvd_mul_right 3 n)))))

end CFSG.StandardType.SCFourCover

end
