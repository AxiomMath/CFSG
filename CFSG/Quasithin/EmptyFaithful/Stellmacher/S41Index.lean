module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.F53.Stellmacher

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem relIndex_sup_right_eq_inf_relIndex {K Q : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (Q : Set G)) :
    Q.relIndex (K ⊔ Q) = (K ⊓ Q).relIndex K := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hK
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hK
  rw [Subgroup.inf_relIndex_left]
  exact (Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient K Q hK).toEquiv).symm

theorem relIndex_two_four_of_not_le {X Q A C : Subgroup G}
    (hQn : X ≤ Subgroup.normalizer (Q : Set G)) (hAX : A ≤ X) (hCX : C ≤ X)
    (h2A : IsPGroup 2 A)
    (hE4 : ((A ⊔ C) ⊓ Q).relIndex (A ⊔ C) ≤ 4)
    (hA : ¬ A ≤ Q) (hAC : ¬ A ⊓ C ≤ Q) (hCA : ¬ C ≤ A ⊔ Q) :
    (A ⊓ Q).relIndex A = 2 ∧ (C ⊓ Q).relIndex C = 4 ∧ A ≤ C ⊔ Q := by
  obtain ⟨n, hn⟩ : ∃ n, Q.relIndex (A ⊔ Q) = 2 ^ n := by
    rw [relIndex_sup_right_eq_inf_relIndex (hAX.trans hQn)]
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2A
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (hm ▸ Subgroup.relIndex_dvd_card (H := A ⊓ Q) (K := A))
    exact ⟨k, hk⟩
  rw [← relIndex_sup_right_eq_inf_relIndex (hAX.trans hQn),
    ← relIndex_sup_right_eq_inf_relIndex (hCX.trans hQn)]
  rw [← relIndex_sup_right_eq_inf_relIndex ((sup_le hAX hCX).trans hQn)] at hE4
  have hQA : Q ≤ A ⊔ Q := le_sup_right
  have hQC : Q ≤ C ⊔ Q := le_sup_right
  have hAE : A ⊔ Q ≤ A ⊔ C ⊔ Q := sup_le_sup_right le_sup_left Q
  have hCE : C ⊔ Q ≤ A ⊔ C ⊔ Q := sup_le_sup_right le_sup_right Q
  have hEpos : 0 < Q.relIndex (A ⊔ C ⊔ Q) :=
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card (H := Q) (K := A ⊔ C ⊔ Q)) Nat.card_pos
  have mAE := Subgroup.relIndex_mul_relIndex Q (A ⊔ Q) (A ⊔ C ⊔ Q) hQA hAE
  have mCE := Subgroup.relIndex_mul_relIndex Q (C ⊔ Q) (A ⊔ C ⊔ Q) hQC hCE
  have ha2 : Q.relIndex (A ⊔ Q) = 2 := by
    have ha1 : Q.relIndex (A ⊔ Q) ≠ 1 := fun h =>
      hA (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h))
    have hle : Q.relIndex (A ⊔ Q) ≤ 4 := (Nat.le_of_dvd hEpos (Dvd.intro _ mAE)).trans hE4
    have ha4 : Q.relIndex (A ⊔ Q) ≠ 4 := by
      intro h4
      rw [h4] at mAE
      have h1 : (A ⊔ Q).relIndex (A ⊔ C ⊔ Q) = 1 := by omega
      exact hCA (le_sup_right.trans (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1)))
    rw [hn] at ha1 hle ha4 ⊢
    have hn3 : n < 3 := by
      by_contra hc
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc)
      omega
    interval_cases n
    · exact absurd rfl ha1
    · rfl
    · exact absurd rfl ha4
  have hACQ : A ≤ C ⊔ Q := by
    have hQL : Q ≤ (A ⊔ Q) ⊓ (C ⊔ Q) := le_inf hQA hQC
    have hm := Subgroup.relIndex_mul_relIndex Q ((A ⊔ Q) ⊓ (C ⊔ Q)) (A ⊔ Q) hQL inf_le_left
    rw [ha2] at hm
    have hL1 : Q.relIndex ((A ⊔ Q) ⊓ (C ⊔ Q)) ≠ 1 := fun h =>
      hAC ((le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans le_sup_left)).trans
        (Subgroup.relIndex_eq_one.mp h))
    have hL2 : ((A ⊔ Q) ⊓ (C ⊔ Q)).relIndex (A ⊔ Q) = 1 := by
      rcases Nat.prime_two.eq_one_or_self_of_dvd _ (Dvd.intro _ hm) with h | h
      · exact absurd h hL1
      · rw [h] at hm
        omega
    exact le_sup_left.trans ((Subgroup.relIndex_eq_one.mp hL2).trans inf_le_right)
  have mAC := Subgroup.relIndex_mul_relIndex Q (A ⊔ Q) (C ⊔ Q) hQA (sup_le hACQ hQC)
  rw [ha2] at mAC
  have hy1 : (A ⊔ Q).relIndex (C ⊔ Q) ≠ 1 := fun h =>
    hCA (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h))
  have hcdvd : Q.relIndex (C ⊔ Q) ∣ Q.relIndex (A ⊔ C ⊔ Q) := Dvd.intro _ mCE
  have hcle : Q.relIndex (C ⊔ Q) ≤ 4 := (Nat.le_of_dvd hEpos hcdvd).trans hE4
  have hcpos : 0 < Q.relIndex (C ⊔ Q) := Nat.pos_of_dvd_of_pos hcdvd hEpos
  exact ⟨ha2, by omega, hACQ⟩

end CFSG.Quasithin.F53.Stellmacher
