module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinNumMain
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringPin

open Finset CFSG.Open
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem NumList46.psl2 {M : ℕ}
    (h : ∃ x d : ℕ, 2 ≤ x ∧ ((Odd x ∧ d = 2) ∨ (Even x ∧ d = 1)) ∧ M * d = x * (x ^ 2 - 1)) :
    NumList46 M := Or.inl h

theorem NumList46.sl3 {M : ℕ}
    (h : ∃ s g d : ℕ, s.Prime ∧ 1 ≤ g ∧ (s = 2 ∨ (5 ≤ s ∧ g ≤ 2)) ∧ d ∣ 3 ∧
    ((d ∣ s ^ g - 1 ∧ M * d = (s ^ g) ^ 3 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 - 1))) ∨
     (d ∣ s ^ g + 1 ∧ M * d = (s ^ g) ^ 3 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1))))) :
    NumList46 M := Or.inr (Or.inl h)

theorem NumList46.sp4 {M : ℕ}
    (h : ∃ s g d : ℕ, s.Prime ∧ 1 ≤ g ∧ (s = 2 ∨ (5 ≤ s ∧ g = 1)) ∧
    ((Even (s ^ g) ∧ d = 1) ∨ (Odd (s ^ g) ∧ d = 2)) ∧
    M * d = (s ^ g) ^ 4 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 4 - 1))) : NumList46 M :=
  Or.inr (Or.inr (Or.inl h))

theorem NumList46.u4 {M : ℕ}
    (h : ∃ s g d : ℕ, s.Prime ∧ 1 ≤ g ∧ (s = 2 ∨ (5 ≤ s ∧ g = 1)) ∧ d ∣ 4 ∧ d ∣ s ^ g + 1 ∧
    M * d = (s ^ g) ^ 6 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1) * ((s ^ g) ^ 4 - 1))) :
    NumList46 M := Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem NumList46.l4 {M : ℕ}
    (h : ∃ s d : ℕ, s.Prime ∧ 5 ≤ s ∧ d ∣ 4 ∧ d ∣ s - 1 ∧
    M * d = s ^ 6 * ((s ^ 2 - 1) * (s ^ 3 - 1) * (s ^ 4 - 1))) : NumList46 M :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem NumList46.g2 {M : ℕ}
    (h : ∃ s g : ℕ, s.Prime ∧ 1 ≤ g ∧ (s = 2 ∨ (5 ≤ s ∧ g = 1)) ∧ M = ordG2 (s ^ g)) :
    NumList46 M := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem NumList46.d4 {M : ℕ} (h : ∃ f : ℕ, 1 ≤ f ∧ M = ordTrialityD4 (2 ^ f)) : NumList46 M :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem NumList46.sz {M : ℕ} (h : ∃ f : ℕ, 1 ≤ f ∧ M = ordSuzuki (2 ^ f)) : NumList46 M :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem NumList46.f4t {M : ℕ} (h : ∃ f : ℕ, 1 ≤ f ∧ M = ordTwistedF4 (2 ^ f)) : NumList46 M :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem NumList46.explicit {M : ℕ} (h : ∃ D ∈ ExplicitD, M ∣ D) : NumList46 M :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))

theorem five_le_of_prime_gt_three {p : ℕ} (hp : p.Prime) (h : 3 < p) : 5 ≤ p := by
  by_contra hc
  have : p = 4 := by omega
  subst this
  exact absurd hp (by norm_num)

theorem num_c1 {X : Type} [Group X]
    (h : ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
      Nonempty (X ≃* projSL 2 (GaloisField p e))) : NumList46 (Nat.card X) := by
  obtain ⟨p, e, hfact, hp2, he, ⟨φ⟩⟩ := h
  have hp : p.Prime := hfact.out
  have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have h1 := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSL_two_mul (GaloisField p e)
  rw [hK, ← Nat.card_congr φ.toEquiv] at h1
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have h2 : 2 ∣ p ^ e - 1 := by
    obtain ⟨c, hc⟩ := hodd
    exact ⟨c, by omega⟩
  rw [Nat.gcd_eq_left h2] at h1
  have h3 : 2 ≤ p ^ e := by
    have := hp.two_le
    exact le_trans this (Nat.le_self_pow (by omega) p)
  exact NumList46.psl2 ⟨p ^ e, 2, h3, Or.inl ⟨hodd, rfl⟩, h1⟩

theorem num_sl3eps {X : Type} [Group X] {s g : ℕ} (hs : s.Prime) (hg : 1 ≤ g)
    (hc : s = 2 ∨ (5 ≤ s ∧ g ≤ 2)) (h : IsSLThreeEpsAt X (s ^ g)) : NumList46 (Nat.card X) := by
  obtain ⟨K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ := h
  · have h1 := CFSG.Open.StatedAPI.card_statedSL_three K
    rw [← Nat.card_congr φ.toEquiv, hK] at h1
    exact NumList46.sl3 ⟨s, g, 1, hs, hg, hc, one_dvd _, Or.inl ⟨one_dvd _, by rw [mul_one, h1]⟩⟩
  · have h1 := CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK
    rw [← Nat.card_congr φ.toEquiv] at h1
    exact NumList46.sl3 ⟨s, g, 1, hs, hg, hc, one_dvd _, Or.inr ⟨one_dvd _, by
      rw [mul_one, h1, mul_assoc]⟩⟩

theorem num_projSL_three {X : Type} [Group X] {s g : ℕ} [Fact s.Prime] (hg : 1 ≤ g)
    (hc : s = 2 ∨ (5 ≤ s ∧ g ≤ 2)) (φ : X ≃* projSL 3 (GaloisField s g)) :
    NumList46 (Nat.card X) := by
  have hK : Nat.card (GaloisField s g) = s ^ g := GaloisField.card s g (by omega)
  have h1 := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSL_three_mul_gcd (GaloisField s g)
  rw [hK, ← Nat.card_congr φ.toEquiv] at h1
  exact NumList46.sl3 ⟨s, g, _, Fact.out, hg, hc, Nat.gcd_dvd_left _ _,
    Or.inl ⟨Nat.gcd_dvd_right _ _, by rw [h1]⟩⟩

theorem num_projSU_three {X : Type} [Group X] {s g : ℕ} [Fact s.Prime] (hg : 1 ≤ g)
    (hc : s = 2 ∨ (5 ≤ s ∧ g ≤ 2)) (φ : X ≃* projSU 3 s g) : NumList46 (Nat.card X) := by
  have h1 := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSU_three_mul_gcd s g hg
  rw [← Nat.card_congr φ.toEquiv] at h1
  exact NumList46.sl3 ⟨s, g, _, Fact.out, hg, hc, Nat.gcd_dvd_left _ _,
    Or.inr ⟨Nat.gcd_dvd_right _ _, by rw [h1]⟩⟩

theorem num_c2 {X : Type} [Group X]
    (h : ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
      (IsSLThreeEpsAt X (p ^ e) ∨ Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨
        Nonempty (X ≃* projSU 3 p e))) : NumList46 (Nat.card X) := by
  obtain ⟨p, e, hfact, hp3, he1, he2, h⟩ := h
  have hc : p = 2 ∨ (5 ≤ p ∧ e ≤ 2) := Or.inr ⟨five_le_of_prime_gt_three hfact.out hp3, he2⟩
  rcases h with h | h | h
  · exact num_sl3eps hfact.out he1 hc h
  · obtain ⟨φ⟩ := h
    exact num_projSL_three he1 hc φ
  · obtain ⟨φ⟩ := h
    exact num_projSU_three he1 hc φ

theorem num_c3 {X : Type} [Group X]
    (h : ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
      (Blueprint.ChevalleyExceptionalModel X .G2 p 1 ∨
        Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
        (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
        (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1))))) :
    NumList46 (Nat.card X) := by
  obtain ⟨p, hfact, hp3, h⟩ := h
  have hp : p.Prime := hfact.out
  have hp5 : 5 ≤ p := five_le_of_prime_gt_three hp hp3
  have hK : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have hodd : Odd (p ^ 1) := by
    rw [pow_one]; exact hp.odd_of_ne_two (by omega)
  rcases h with hG | hSp | hSU | hSL
  · have h1 := (CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hG).1 rfl
    exact NumList46.g2 ⟨p, 1, hp, le_rfl, Or.inr ⟨hp5, rfl⟩, h1⟩
  · obtain ⟨φ⟩ := hSp
    have h2 : (2 : GaloisField p 1) ≠ 0 := by
      apply Ring.two_ne_zero
      rw [ringChar.eq (GaloisField p 1) p]
      omega
    have h1 := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSp_two_mul (GaloisField p 1) h2
    rw [hK, ← Nat.card_congr φ.toEquiv] at h1
    exact NumList46.sp4 ⟨p, 1, 2, hp, le_rfl, Or.inr ⟨hp5, rfl⟩, Or.inr ⟨hodd, rfl⟩, h1⟩
  · obtain ⟨-, ⟨φ⟩⟩ := hSU
    have h1 := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSU_four_mul p 1 le_rfl
    rw [← Nat.card_congr φ.toEquiv] at h1
    exact NumList46.u4 ⟨p, 1, _, hp, le_rfl, Or.inr ⟨hp5, rfl⟩, Nat.gcd_dvd_left _ _,
      Nat.gcd_dvd_right _ _, h1⟩
  · obtain ⟨-, ⟨φ⟩⟩ := hSL
    have h1 := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSL_four_mul (GaloisField p 1)
    rw [hK, ← Nat.card_congr φ.toEquiv, pow_one] at h1
    exact NumList46.l4 ⟨p, _, hp, hp5, Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _, h1⟩

end CFSG.RankThree.PartTwo.Sec4.HeringPin
