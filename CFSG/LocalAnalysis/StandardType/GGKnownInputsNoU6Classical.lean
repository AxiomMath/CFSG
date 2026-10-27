module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGKnownInputsPsuOrderClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open

theorem largeEvenLabelAll_markedModel_classical {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) :
    LargeEvenLabelAll lab fun R _ _ _ => MarkedModel lab R := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at h hn hl
  rcases h with rfl | rfl | rfl | rfl
  · obtain ⟨hl1, hl2⟩ := hl
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeLinear_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    refine Or.inl ⟨by decide, statedClassicalModel_linear (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_, fun h => ?_⟩⟩
    · simp only [Prod.mk.injEq] at h
      have := four_le_two_pow (hl2 (by omega))
      omega
    · simp only [Prod.mk.injEq] at h
      exact two_pow_ne_three n h.2
  · obtain ⟨hl1, hl2⟩ := hl
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  · obtain ⟨hl1, hl2⟩ := hl
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  · dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    split_ifs at hQ ⊢ with h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
      exact Or.inl ⟨by decide, statedClassicalModel_linear 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp, by simp⟩⟩
    · refine recipeOmegaPlus_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
      exact Or.inl ⟨by decide, statedClassicalModel_omegaPlus l n hK
        ⟨Nat.prime_two, hn, by omega⟩⟩

private theorem card_largeEvenProj_SU_ppd {N g : ℕ} (hN : 1 ≤ N) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ g) ^ 2) :
    1 ≤ g ∧ Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ g))) =
      ordTwistedA N (2 ^ g) := by
  have hg : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact h
  refine ⟨hg, ?_⟩
  change Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU (N + 1) (2 ^ g) K)) = _
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hg hK (by omega),
    CFSG.Open.ordTwistedA, Nat.add_sub_cancel, Nat.mul_comm (N + 1) N]

theorem ordTwistedA_five_dvd_card_of_twA_marking {R : Type} [Group R] {J : Subgroup R} {n : ℕ}
    (hmark : LargeEvenMarking ↥J (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩)) :
    1 ≤ n ∧ ordTwistedA 5 (2 ^ n) ∣ Nat.card R := by
  obtain ⟨-, lab', -, hraw⟩ := hmark
  obtain ⟨_, _, _, _, -, -, -, rfl⟩ := largeEvenRawDatum_exists hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, _, _, hK, -, -, θ, -⟩ := hraw
  obtain ⟨hn, hc⟩ := card_largeEvenProj_SU_ppd (N := 5) (by norm_num) hK
  refine ⟨hn, ?_⟩
  rw [← hc, ← Nat.card_congr θ.toEquiv]
  exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J)

private theorem noU6_of_not_dvd_card {R : Type} [Group R] {g : ℕ}
    (h : ∀ n, 1 ≤ n → g ∣ n → ¬ ordTwistedA 5 (2 ^ n) ∣ Nat.card R) :
    ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → g ∣ n →
      ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) := by
  intro J₁ n _ hgn hmark
  obtain ⟨hn, hdvd⟩ := ordTwistedA_five_dvd_card_of_twA_marking hmark
  exact h n hn hgn hdvd

theorem largeEvenLabelAll_noU6_A {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A) (hrank : lab.rank ≤ 8) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → lab.n ∣ n →
      ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) := by
  refine fun Q hQ => largeEvenRawDatum_mono (fun R _ _ _ hq => ⟨hq.1, ?_⟩)
    (largeEvenLabelAll_markedModel_classical hlab (Or.inl htag) Q hQ)
  obtain ⟨t, l, g⟩ := lab
  dsimp only at htag hrank ⊢
  subst htag
  obtain ⟨hg, hl1, -⟩ := hlab
  have hcard : Nat.card R = ordA l (2 ^ g) :=
    CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
      (show LieModel R .PSL (l + 1) 2 g from hq.2)
  refine noU6_of_not_dvd_card fun n hn hgn hdvd => ?_
  rw [hcard] at hdvd
  exact not_ordTwistedA_five_dvd_ordA hg hn hgn hl1 hrank hdvd

theorem largeEvenLabelAll_noU6_BC {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .B ∨ lab.tag = .C) (hrank : lab.rank ≤ 4) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → lab.n ∣ n →
      ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) := by
  refine fun Q hQ => largeEvenRawDatum_mono (fun R _ _ _ hq => ⟨hq.1, ?_⟩)
    (largeEvenLabelAll_markedModel_classical hlab (by tauto) Q hQ)
  obtain ⟨t, l, g⟩ := lab
  dsimp only at htag hrank ⊢
  have hg : 1 ≤ g := hlab.1
  have hcard : Nat.card R = ordBC l (2 ^ g) := by
    rcases htag with rfl | rfl <;>
      exact CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
        (show LieModel R .PSp l 2 g from hq.2)
  refine noU6_of_not_dvd_card fun n hn hgn hdvd => ?_
  rw [hcard] at hdvd
  exact not_ordTwistedA_five_dvd_ordBC hg hn hgn hrank hdvd

theorem largeEvenLabelAll_noU6_D {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .D) (hrank : lab.rank ≤ 5) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → lab.n ∣ n →
      ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) := by
  refine fun Q hQ => largeEvenRawDatum_mono (fun R _ _ _ hq => ⟨hq.1, ?_⟩)
    (largeEvenLabelAll_markedModel_classical hlab (Or.inr (Or.inr (Or.inr htag))) Q hQ)
  obtain ⟨t, l, g⟩ := lab
  dsimp only at htag hrank ⊢
  subst htag
  obtain ⟨hg, hl3⟩ := hlab
  dsimp only at hg hl3
  by_cases h3 : l = 3
  · subst h3
    have hcard : Nat.card R = ordA 3 (2 ^ g) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
        (show LieModel R .PSL 4 2 g from hq.2)
    refine noU6_of_not_dvd_card fun n hn hgn hdvd => ?_
    rw [hcard] at hdvd
    exact not_ordTwistedA_five_dvd_ordA hg hn hgn (by norm_num) (by norm_num) hdvd
  · have hM : LieModel R .POmegaPlus l 2 g := by
      have := hq.2
      simpa only [MarkedModel, markTag, markRank, markChar, markDeg, h3, if_false] using this
    have hcard : Nat.card R = ordD l (2 ^ g) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hM
    refine noU6_of_not_dvd_card fun n hn hgn hdvd => ?_
    rw [hcard] at hdvd
    exact not_ordTwistedA_five_dvd_ordD hg hn hgn (by omega) hrank hdvd

end CFSG.StandardType.SCFourCover

end
