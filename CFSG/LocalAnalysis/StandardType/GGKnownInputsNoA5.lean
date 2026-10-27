module

public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTableB
public import CFSG.LocalAnalysis.StandardType.GGKnownInputsPsuOrder

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open

theorem largeEvenLabelAll_markedModel_f4e6 {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .F4 ∨ lab.tag = .twF4 ∨ lab.tag = .E6) :
    LargeEvenLabelAll lab fun R _ _ _ => MarkedModel lab R := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at h hn
  rcases h with rfl | rfl | rfl
  · dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeChevalley_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .F4 hK⟩)
  · dsimp only at hl
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by omega
    dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeTwF4_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    have hRee := reeTitsRelationModel_largeEven ((n - 1) / 2) hK
    rw [← hn'] at hRee
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, rfl, ⟨k, hk⟩, hn3⟩,
      (n - 1) / 2, hn', hRee⟩))
  · dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg] at hQ ⊢
    refine recipeChevalley_imp (fun K _ _ hK I F hq => ⟨hq, ?_⟩) hQ
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E6 hK⟩)

section Certs


theorem ordTwistedA_five_dvd_card_of_marking {R : Type} [Group R] {J : Subgroup R} {n : ℕ}
    (hmark : LargeEvenMarking ↥J (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩)) :
    1 ≤ n ∧ ordTwistedA 5 (2 ^ n) ∣ Nat.card R := by
  obtain ⟨lab, hlab, R', _, I', F', θ, -, -, rfl, hM⟩ :=
    largeEvenMarking_exists_markedModel hmark
  have hM' : LieModel R' .PSU 6 2 n := hM
  have hc : Nat.card R' = ordTwistedA 5 (2 ^ n) :=
    CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM'
  refine ⟨hlab.1, ?_⟩
  rw [← hc, ← Nat.card_congr θ.toEquiv]
  exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J)

theorem largeEvenLabelAll_no_twA_five_marking {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .F4 ∨ lab.tag = .twF4 ∨ lab.tag = .E6) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J : Subgroup R) (n : ℕ),
      LargeEvenMarking ↥J (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) → lab.n ∣ n → False := by
  refine LargeEvenLabelAll.mono (fun R _ _ _ hM J n hmark hgn => ?_)
    (largeEvenLabelAll_markedModel_f4e6 hlab h)
  obtain ⟨hn, hdvd⟩ := ordTwistedA_five_dvd_card_of_marking hmark
  obtain ⟨t, l, g⟩ := lab
  obtain ⟨hg, -⟩ := hlab
  dsimp only at h hg hgn
  rcases h with rfl | rfl | rfl
  · rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder (show LieModel R .F4 0 2 g from hM)]
      at hdvd
    exact not_ordTwistedA_five_dvd_ordF4 hg hn hgn hdvd
  · rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder
      (show LieModel R .twistedF4 0 2 g from hM)] at hdvd
    exact not_ordTwistedA_five_dvd_ordTwistedF4 hg hn hgn hdvd
  · rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder (show LieModel R .E6 0 2 g from hM)]
      at hdvd
    exact not_ordTwistedA_five_dvd_ordE6 hg hn hgn hdvd

end Certs

end CFSG.StandardType.SCFourCover

end
