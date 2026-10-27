module

public import CFSG.RankThree.PartOne.FOCD.ClassicalOuter

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem mem_zpowers_of_commute_of_not_sq_dvd {p : ℕ} {T : Type} [Group T] [Finite T]
    (hp : p.Prime) (hT : ¬ p ^ 2 ∣ Nat.card T) {b y : T} (hbp : b ^ p = 1) (hb1 : b ≠ 1)
    (hyp : y ^ p = 1) (hby : b * y = y * b) : y ∈ Subgroup.zpowers b := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hZb : IsPGroup p (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hZy : IsPGroup p (Subgroup.zpowers y) := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hyp) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers b : Set T) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_left (show Commute b y from hby) k).eq
  have hsup : IsPGroup p ↥(Subgroup.zpowers y ⊔ Subgroup.zpowers b) :=
    hZy.to_sup_of_normal_right' hZb hnorm
  obtain ⟨P, hP⟩ := hsup.exists_le_sylow
  have hcardP : Nat.card P = p ^ (Nat.card T).factorization p := Sylow.card_eq_multiplicity P
  have hfac : (Nat.card T).factorization p ≤ 1 := by
    by_contra hlt
    push Not at hlt
    exact hT ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 hlt)
  have hPle : Nat.card (P : Subgroup T) ≤ p := by
    rw [hcardP]
    calc p ^ (Nat.card T).factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hfac
      _ = p := pow_one p
  have hbP : Subgroup.zpowers b ≤ (P : Subgroup T) := le_trans le_sup_right hP
  have hcardb : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hord]
  have hEq : Subgroup.zpowers b = (P : Subgroup T) :=
    Subgroup.eq_of_le_of_card_ge hbP (by rw [hcardb]; exact hPle)
  rw [hEq]
  exact (le_trans le_sup_left hP) (Subgroup.mem_zpowers y)

theorem innerComp_of_not_sq_dvd {p : ℕ} {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hp : p.Prime) (hT : ¬ p ^ 2 ∣ Nat.card T) : InnerComp p T := by
  intro _ b y hbp hyp hby E hE
  by_cases hb1 : b = 1
  · subst hb1
    rw [centralizer_one_eq_top] at hE
    have hs : IsSimpleGroup ↥(⊤ : Subgroup T) := Subgroup.topEquiv.isSimpleGroup
    have hEtop : E = ⊤ := @eq_of_isComponentOf_simple T _ ⊤ E hs hE
    rw [hEtop]
    exact Subgroup.mem_sup_left (Subgroup.mem_top y)
  · have hy := mem_zpowers_of_commute_of_not_sq_dvd hp hT hbp hb1 hyp hby
    have hbC : b ∈ Subgroup.centralizer (E : Set T) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.1 (hE.1 he)
    exact Subgroup.mem_sup_right ((Subgroup.zpowers_le.2 hbC) hy)

theorem fieldInnerT_of_not_sq_dvd {p : ℕ} {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hp : p.Prime) (hT : ¬ p ^ 2 ∣ Nat.card T)
    (hout : ¬ p ∣ Nat.card (Outer T)) : FieldInnerT p T :=
  fieldInnerT_of_comp (center_eq_bot_of_nonab ‹IsSimpleGroup T› hnab)
    (innerComp_of_not_sq_dvd hp hT) (outerComp_of_not_dvd_outer hp (dvd_refl _) hout)

end CFSG.RankThree.PartOne.FOCD
