module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Odd
public import CFSG.Quasithin.EmptyFaithful.S152NWreath
public import CFSG.Quasithin.EmptyFaithful.S152U18

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem exists_isHStar_le {T M K : Subgroup G} (hK : InH T K) (hKM : ¬ K ≤ M) :
    ∃ H : Subgroup G, IsHStar T M H ∧ H ≤ K := by
  obtain ⟨H, ⟨hH1, hH2, hHK⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    {H : Subgroup G | InH T H ∧ ¬ H ≤ M ∧ H ≤ K} ⟨K, hK, hKM, le_rfl⟩
  refine ⟨H, ⟨hH1, hH2, fun Y hY hYH hYM => ?_⟩, hHK⟩
  by_contra hne
  exact hmin Y ⟨hY, hYM, hYH.trans hHK⟩ (lt_of_le_of_ne hYH hne)

theorem not_nine_dvd_sup {Y T : Subgroup G} (hT : T ≤ Subgroup.normalizer (Y : Set G))
    (hT2 : IsPGroup 2 T) (h : (pCoreOf 2 Y).relIndex Y = 3) : ¬ 9 ∣ Nat.card ↥(Y ⊔ T) := by
  obtain ⟨a, ha⟩ := exists_card_eq_three_mul h
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hT2
  have h1 : Y.relIndex (T ⊔ Y) = Y.relIndex T := relIndex_sup_eq_of_le_normalizer' hT
  have h2 := Subgroup.relIndex_mul_card Y (Y ⊔ T)
  rw [inf_of_le_left le_sup_left, sup_comm Y T, h1, ha] at h2
  have h3 := Subgroup.relIndex_mul_card Y T
  have h4 : Y.relIndex T ∣ 2 ^ b := hb ▸ Dvd.intro _ h3
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
  rw [hc] at h2
  intro h9
  rw [sup_comm Y T, ← h2] at h9
  have h5 : 2 ^ c * (3 * 2 ^ a) = 3 * 2 ^ (c + a) := by ring
  rw [h5] at h9
  have h6 : 3 * 3 ∣ 3 * 2 ^ (c + a) := by simpa using h9
  have h7 : 3 ∣ 2 ^ (c + a) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h6
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h7) (by norm_num)

theorem Y0_le_M (h08 : StageLemma15208) {T Mc M : Subgroup G} (hs : Setting152 T Mc M)
    {Y₀ : Subgroup G} (hTY : T ≤ Subgroup.normalizer (Y₀ : Set G))
    (h3 : (pCoreOf 2 Y₀).relIndex Y₀ = 3) (hne : pCoreOf 2 Y₀ ≠ ⊥) : Y₀ ≤ M := by
  by_contra hY
  have hT2 : IsPGroup 2 T := hs.qtfe.sylow.1
  have hN : InH T (Y₀ ⊔ T) := by
    refine ⟨le_sup_right, ?_⟩
    have hle : pCoreOf 2 Y₀ ≤ pCoreOf 2 (Y₀ ⊔ T) := by
      refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y₀).trans le_sup_left) ?_
        (pCoreOf_isPGroup 2 Y₀)
      exact sup_le (le_normalizer_pCoreOf 2 Y₀) (hTY.trans (normalizer_le_normalizer_pCoreOf 2 Y₀))
    intro hbot
    exact hne (le_bot_iff.mp (hbot ▸ hle))
  have hNM : ¬ Y₀ ⊔ T ≤ M := fun h => hY (le_sup_left.trans h)
  obtain ⟨H', hH', hH'le⟩ := exists_isHStar_le hN hNM
  obtain ⟨e⟩ := h08 G T Mc M hs H' hH'
  have h72 : Nat.card (OTwoQuot H') = 72 := by
    rw [Nat.card_congr e.toEquiv]
    exact S152N.W3.card_eq
  have h9 : 9 ∣ Nat.card ↥(Y₀ ⊔ T) := by
    have h1 : Nat.card (OTwoQuot H') ∣ Nat.card H' := Subgroup.card_quotient_dvd_card _
    have h2 : Nat.card H' ∣ Nat.card ↥(Y₀ ⊔ T) := Subgroup.card_dvd_of_le hH'le
    exact Dvd.dvd.trans (by rw [h72]; norm_num) (h1.trans h2)
  exact not_nine_dvd_sup hTY hT2 h3 h9

theorem Y0_le_cv (h08 : StageLemma15208) {T Mc M H : Subgroup G}
    {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G} (hs : Setting152 T Mc M)
    (hD : Inputs152 T Mc M H B₀ I) {Y₀ : Subgroup G}
    (hTY : T ≤ Subgroup.normalizer (Y₀ : Set G)) (hY : Y₀ = oTwoUpper Y₀)
    (h3 : (pCoreOf 2 Y₀).relIndex Y₀ = 3) (hne : pCoreOf 2 Y₀ ≠ ⊥) (hYMc : Y₀ ≤ Mc) :
    Y₀ ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := by
  have hYM : Y₀ ≤ M := Y0_le_M h08 hs hTY h3 hne
  have := oTwoUpper_le_cv_of_le_Mc hs hD hYM hYMc
  rwa [← hY] at this

end CFSG.Quasithin.S15221
