module

public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.StandardType.GGCompFieldCatalogue

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem twoPowSix_dvd_evenLieOrder_of_badTag {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (hbad : lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der) :
    2 ^ 6 ∣ CFSG.SeitzReduction.F4Pilot.evenLieOrder (markTag lab) (markRank lab)
      (markDeg lab) := by
  obtain ⟨tag, rank, n⟩ := lab
  rcases hbad with ht | ht | ht
  · subst ht
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, -, h3⟩ := hlab
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
    have hfac : (2 ^ n) ^ 2 ∣ CFSG.Open.ordSuzuki (2 ^ n) := by
      unfold CFSG.Open.ordSuzuki
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have hpow : 2 ^ 6 ∣ (2 ^ n) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega : 6 ≤ n * 2)
    exact hpow.trans hfac
  · subst ht
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, -, h3⟩ := hlab
    simp only [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder]
    have hfac : (2 ^ n) ^ 12 ∣ CFSG.Open.ordTwistedF4 (2 ^ n) := by
      unfold CFSG.Open.ordTwistedF4
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_right _ _) _) _) _
    have hpow : 2 ^ 6 ∣ (2 ^ n) ^ 12 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega : 6 ≤ n * 12)
    exact hpow.trans hfac
  · subst ht
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, hn1⟩ := hlab
    subst hn1
    norm_num [markTag, markRank, markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder,
      CFSG.Open.ordTits]

theorem ggChevStMarking_of_compFieldDataQ
    {G : Type} [Group G] {q : ℕ} {X : Subgroup G} (h : GGCompFieldDataQ q X)
    (hm : LargeEvenMarking ↥X (fun _ _ _ _ _ _ => True)) :
    LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GGChevStTag lab) := by
  rcases h with ⟨m, hm1, hfield⟩ | ⟨hq, hord⟩
  ·
    obtain ⟨lab, hlab, -, -, h1, h2, h3, hhas, -⟩ := hfield
    obtain ⟨hcomm0, lab0, hlab0, hraw0⟩ := hm
    obtain ⟨R0, _, I0, F0, hs0, hna0, hθ0⟩ := largeEvenRawDatum_exists hraw0
    obtain ⟨θ0, -⟩ := hθ0
    haveI : IsSimpleGroup R0 := hs0
    refine ⟨hcomm0, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono (fun R' _ I' F' he => ?_) hhas
    obtain ⟨e⟩ := he
    exact ⟨(θ0.symm.trans e).symm.isSimpleGroup,
      nonabelian_of_mulEquiv (θ0.symm.trans e) hna0, e, h1, h2, h3⟩
  ·
    obtain ⟨hcomm, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hm
    obtain ⟨R, _, I, F, hs, hna, hθ⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨θ, -, hM⟩ := hθ
    have htag : GGChevStTag lab := by
      by_cases hbad : lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der
      · exfalso
        have hchar : markChar lab = 2 := by
          rcases hbad with h | h | h <;> simp [markChar, h]
        have hLM : LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
          unfold MarkedModel at hM
          rwa [hchar] at hM
        have h2dvd : 2 ^ 6 ∣ Nat.card R := by
          rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hLM]
          exact twoPowSix_dvd_evenLieOrder_of_badTag hlab hbad
        have hcardR : Nat.card R = 360 ∨ Nat.card R = 6048 := by
          rcases hord with h360 | h6048
          · left; rw [← Nat.card_congr θ.toEquiv]; exact h360
          · right; rw [← Nat.card_congr θ.toEquiv]; exact h6048
        have hnot : ¬ 2 ^ 6 ∣ Nat.card R := by
          rcases hcardR with h360 | h6048
          · rw [h360]; norm_num
          · rw [h6048]; norm_num
        exact hnot h2dvd
      · exact ⟨fun h => hbad (Or.inl h), fun h => hbad (Or.inr (Or.inl h)),
          fun h => hbad (Or.inr (Or.inr h))⟩
    refine ⟨hcomm, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono (fun R' _ I' F' hQ => ?_) hraw
    obtain ⟨hs', hna', hθ'M⟩ := hQ
    obtain ⟨θ', -, -⟩ := hθ'M
    exact ⟨hs', hna', θ', htag⟩

end CFSG.StandardType
