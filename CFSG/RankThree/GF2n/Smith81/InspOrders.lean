module

public import CFSG.RankThree.GF2n.Smith81.InspLinCore
public import CFSG.RankThree.GF2n.Smith81.Smith219Arith

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem factorization_two_card_of_lieModel {Y : Type} [Group Y] {t : StatedLieTag} {k f : ℕ}
    (hf : 1 ≤ f) (htag : TimmesfeldTag t k f) (hL : LieModel Y t k 2 f) :
    (Nat.card Y).factorization 2 = f * Smith219Arith.sylowExp t k := by
  rcases htag with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨ht, hk⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, ht⟩
  · have hcard := (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).1 rfl
    have hpr : Profile (Nat.card Y) (f * ((k - 1) * (k - 1 + 1) / 2)) (zA (k - 1) f) := by
      rw [hcard]
      exact profile_ordA (by omega) hf
    rw [factorization_two_of_profile hpr]
    simp only [Smith219Arith.sylowExp]
    rw [show k - 1 + 1 = k by omega, Nat.mul_comm (k - 1) k]
  · have hcard := (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).2.2.1 rfl
    have hpr : Profile (Nat.card Y) (f * (k * k)) (zBC k f) := by
      rw [hcard]
      exact profile_ordBC hf
    rw [factorization_two_of_profile hpr]
    rfl
  · rcases ht with rfl | rfl
    · have hcard :=
        (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).2.2.2.1 rfl
      have hpr : Profile (Nat.card Y) (f * (k * (k - 1))) (zD k f) := by
        rw [hcard]
        exact profile_ordD (by omega) hf
      rw [factorization_two_of_profile hpr]
      rfl
    · have hcard :=
        (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).2.2.2.2 rfl
      have hpr : Profile (Nat.card Y) (f * (k * (k - 1))) (z2D k f) := by
        rw [hcard]
        exact profile_ordTwistedD (by omega) hf
      rw [factorization_two_of_profile hpr]
      rfl
  · have hcard := card_chevalleyExceptionalModel_two (hL.chevalleyExceptionalModel (by decide))
    have hpr : Profile (Nat.card Y) (f * 6) (zG2 f) := by
      rw [hcard]
      exact profile_ordG2 hf
    rw [factorization_two_of_profile hpr]
    rfl
  · have hcard := card_chevalleyExceptionalModel_two (hL.chevalleyExceptionalModel (by
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [factorization_two_of_profile (Z := zD4 f) (N := f * 12)
        (by rw [hcard]; exact profile_ordTrialityD4 hf)]
      rfl
    · rw [factorization_two_of_profile (Z := zF4 f) (N := f * 24)
        (by rw [hcard]; exact profile_ordF4 hf)]
      rfl
    · rw [factorization_two_of_profile (Z := zE6 f) (N := f * 36)
        (by rw [hcard]; exact profile_ordE6 hf)]
      rfl
    · rw [factorization_two_of_profile (Z := z2E6 f) (N := f * 36)
        (by rw [hcard]; exact profile_ordTwistedE6 hf)]
      rfl
    · rw [factorization_two_of_profile (Z := zE7 f) (N := f * 63)
        (by rw [hcard]; exact profile_ordE7 hf)]
      rfl
    · rw [factorization_two_of_profile (Z := zE8 f) (N := f * 120)
        (by rw [hcard]; exact profile_ordE8 hf)]
      rfl

end CFSG.RankThree.GF2n.Smith81.Insp
