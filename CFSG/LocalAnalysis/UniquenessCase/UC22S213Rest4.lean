module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicLocal17
import CFSG.LocalAnalysis.UniquenessCase.UC22S213CenterZ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3ClosedZ (L : Subgroup G) : Prop :=
  (∃ m : ℕ, 8 ≤ m ∧ IsAlt (BarInf L) m) ∨ IsSpor (BarInf L) .M11 ∨ IsSpor (BarInf L) .M23 ∨
    IsSpor (BarInf L) .HS ∨ IsSpor (BarInf L) .J2 ∨ IsSpor (BarInf L) .He ∨
    (∃ p e : ℕ, p.Prime ∧ 5 ≤ p ∧ 2 ≤ e ∧ LieModel (BarInf L) .PSL 2 p e) ∨
    LieModel (BarInf L) .PSL 5 2 1

@[expose] def S21_3Rest4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem uc22s213_closed_or_closed2_of_closedZ (hGA : GriessAllModelsStatement)
    (hSC : PartTwo.Inputs1719.K_SporadicCoverCenterOdd) {M L : Subgroup G} (hL : L ∈ calC M)
    (h : S21_3ClosedZ L) : S21_3Closed L ∨ S21_3Closed2 L := by
  have hnd : ∀ {r : ℕ}, 2 ≤ r → center (Bar2 L) = ⊥ → ¬ r ∣ Nat.card (center (Bar2 L)) := by
    intro r hr hc hd
    rw [hc, Subgroup.card_bot, Nat.dvd_one] at hd
    omega
  rcases h with ⟨m, hm, hX⟩ | hX | hX | hX | hX | hX | ⟨p, e, hp, hp5, he, hX⟩ | hX
  · exact .inl ⟨hnd (by norm_num) (uc22s213_center_bar2_eq_bot_of_isAlt hL hm hX),
      .inl ⟨m, by omega, hX⟩⟩
  · exact .inl ⟨hnd (by norm_num)
      (uc22s213_center_bar2_eq_bot_of_isSpor hSC hL (.inl rfl) hX), .inr (.inl hX)⟩
  · exact .inl ⟨hnd (by norm_num)
      (uc22s213_center_bar2_eq_bot_of_isSpor hSC hL (.inr (.inl rfl)) hX),
      .inr (.inr (.inr (.inl hX)))⟩
  · exact .inl ⟨hnd (by norm_num)
      (uc22s213_center_bar2_eq_bot_of_isSpor hSC hL (.inr (.inr (.inl rfl))) hX),
      .inr (.inr (.inr (.inr hX)))⟩
  · exact .inr (.inr (.inl ⟨hnd (by norm_num)
      (uc22s213_center_bar2_eq_bot_of_isSpor hSC hL (.inr (.inr (.inr (.inl rfl)))) hX),
      .inl hX⟩))
  · exact .inr (.inr (.inl ⟨hnd (by norm_num)
      (uc22s213_center_bar2_eq_bot_of_isSpor hSC hL (.inr (.inr (.inr (.inr rfl)))) hX),
      .inr hX⟩))
  · exact .inr (.inr (.inr (.inl ⟨p, e, hp, hp5, he,
      hnd hp.two_le (uc22s213_center_bar2_eq_bot_of_psl2 hGA hL hp5 hX), hX⟩)))
  · exact .inr (.inr (.inr (.inr ⟨hnd (by norm_num)
      (uc22s213_center_bar2_eq_bot_of_psl_five_two hGA hL hX), hX⟩)))

theorem s21_3Rest3_of_rest4 (hGA : GriessAllModelsStatement)
    (hSC : PartTwo.Inputs1719.K_SporadicCoverCenterOdd) {D : Data G} {Ch : Choice2011 G}
    (h : S21_3Rest4 D Ch) : S21_3Rest3 D Ch :=
  fun hH c L hL hC hC2 =>
    h hH c L hL hC hC2 fun hZ => (uc22s213_closed_or_closed2_of_closedZ hGA hSC hL hZ).elim hC hC2

end CFSG.LocalAnalysis.UniquenessCase.UC22
