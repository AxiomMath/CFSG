module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementTheta
public import CFSG.Assembly.OrderReductions.PrimePart

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.OrderReductions.PrimePart

universe u

variable {G : Type u} [Group G] [Finite G]

theorem normal_join_prime_part {p : ℕ} (hp : p.Prime)
    (T C : Subgroup G) [T.Normal] (hC : Nat.Coprime p (Nat.card C)) :
    primePart p (Nat.card (T ⊔ C : Subgroup G)) = primePart p (Nat.card T) := by
  have hidx : T.relIndex (T ⊔ C) ∣ Nat.card C := by
    rw [Subgroup.relIndex_sup_left]
    exact T.relIndex_dvd_card C
  have hnot : ¬ p ∣ T.relIndex (T ⊔ C) :=
    fun h => (hp.coprime_iff_not_dvd.mp hC) (h.trans hidx)
  have hcard : Nat.card T * T.relIndex (T ⊔ C) =
      Nat.card (T ⊔ C : Subgroup G) := by
    have h := (T.subgroupOf (T ⊔ C)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at h
    exact h
  have hidxne : T.relIndex (T ⊔ C) ≠ 0 := by
    intro hzero
    have hzeroCard : Nat.card (T ⊔ C : Subgroup G) = 0 := by
      rw [← hcard, hzero, mul_zero]
    exact Nat.card_pos.ne' hzeroCard
  rw [← hcard, primePart_mul p _ _ Nat.card_pos.ne' hidxne]
  simp only [primePart, Nat.factorization_eq_zero_of_not_dvd hnot, pow_zero, mul_one]

theorem normal_join_supplied_sylow {p : ℕ} (hp : p.Prime)
    (T C : Subgroup G) [T.Normal] (hC : Nat.Coprime p (Nat.card C))
    (Q : Sylow p T) :
    ∃ S : Sylow p (T ⊔ C : Subgroup G),
      (S : Subgroup (T ⊔ C : Subgroup G)).map (T ⊔ C : Subgroup G).subtype =
        (Q : Subgroup T).map T.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  apply exists_sylow_image_of_card p ((Q : Subgroup T).map T.subtype) (T ⊔ C)
    ((Subgroup.map_subtype_le _).trans le_sup_left)
  rw [sylow_map_card_eq_primePart, normal_join_prime_part hp T C hC]

theorem canonical_theta_join_properties {p : ℕ} (hp : p.Prime)
    (D T : Subgroup G) (hTD : T ≤ D)
    (hTnormal : (T.subgroupOf D).Normal) (hTodd : Odd (Nat.card T)) :
    let Theta := minimalLocalFailurePairConfinementTheta p D
    let U := T ⊔ Theta
    U ≤ D ∧ (U.subgroupOf D).Normal ∧ Odd (Nat.card U) ∧
      primePart p (Nat.card U) = primePart p (Nat.card T) ∧
      ∀ Q : Sylow p T, ∃ S : Sylow p U,
        (S : Subgroup U).map U.subtype = (Q : Subgroup T).map T.subtype := by
  let Theta := minimalLocalFailurePairConfinementTheta p D
  let U := T ⊔ Theta
  have hThetaD : Theta ≤ D := pairConfinement_theta_le p D
  have hUD : U ≤ D := sup_le hTD hThetaD
  let : (T.subgroupOf D).Normal := hTnormal
  let : (Theta.subgroupOf D).Normal := pairConfinement_theta_normal p D
  have hUnormal : (U.subgroupOf D).Normal := by
    dsimp only [U]
    rw [Subgroup.subgroupOf_sup hTD hThetaD]
    infer_instance
  have hTcard : Nat.card (T.subgroupOf D) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTD).toEquiv
  have hThetacard : Nat.card (Theta.subgroupOf D) = Nat.card Theta :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hThetaD).toEquiv
  have hUcard : Nat.card (U.subgroupOf D) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUD).toEquiv
  obtain ⟨hThetaodd, hThetacoprime⟩ := pairConfinement_theta_order p hp D
  have hUodd : Odd (Nat.card U) := by
    rw [← hUcard]
    dsimp only [U]
    rw [Subgroup.subgroupOf_sup hTD hThetaD]
    exact CFSG.ComponentClassification.OddCore.odd_card_sup _ _
      (hTcard.symm ▸ hTodd) (hThetacard.symm ▸ hThetaodd)
  have hpart : primePart p (Nat.card U) = primePart p (Nat.card T) := by
    have h := normal_join_prime_part hp (T.subgroupOf D) (Theta.subgroupOf D)
      (hThetacard.symm ▸ hThetacoprime)
    rw [← Subgroup.subgroupOf_sup hTD hThetaD, hUcard, hTcard] at h
    exact h
  refine ⟨hUD, hUnormal, hUodd, hpart, ?_⟩
  intro Q
  let : Fact p.Prime := ⟨hp⟩
  apply exists_sylow_image_of_card p ((Q : Subgroup T).map T.subtype) U
    ((Subgroup.map_subtype_le _).trans le_sup_left)
  rw [sylow_map_card_eq_primePart, hpart]

end CFSG.ShultStronglyClosedTI.LocalTheta
