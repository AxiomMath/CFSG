module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAltA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} {A : Subgroup (MulAut X)}
  {Z₁ : Subgroup X} {r : ℕ}

theorem center_eq_of_alt3 {G : Type} [Group G] [Finite G] (hF : BarFacts X S A Z₁ r)
    (g3 : W3Lem85TwoGap3 G) (hc : Nat.card (Subgroup.center X) = 3)
    (hs : SevenElevenASixShape X S) : Z₁ = Subgroup.center X := by
  by_contra hne
  have hle : Z₁ ≤ Subgroup.center X := hF.le_center
  have hbot : Z₁ = ⊥ := by
    have hdvd : Nat.card Z₁ ∣ 3 := hc ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq Z₁ h1
    · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, h3])) hne
  have hinv : ∀ a ∈ A, ∀ q ∈ Subgroup.center X, a q ∈ Subgroup.center X := by
    intro a _ q hq
    rw [Subgroup.mem_center_iff] at hq ⊢
    intro x
    have hx := hq (a.symm x)
    calc x * a q = a (a.symm x) * a q := by simp
      _ = a (a.symm x * q) := by rw [map_mul]
      _ = a (q * a.symm x) := by rw [hx]
      _ = a q * x := by rw [map_mul]; simp
  have hcent : ∀ a ∈ A, ∀ z ∈ Subgroup.center X, a z = z := by
    intro a ha z hz
    have h1 := hF.oddComm (Subgroup.center X) (by rw [hc]; decide) hinv a ha z hz
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  have h2 := g3.1 X S hF.situation hc hs A hF.elemAbelian hF.fixes hcent
  have h3 := hF.card_lt
  have h4 := hF.card_eq
  omega

theorem barConcl_of_alt4 (hF : BarFacts X S A Z₁ r) (g1 : W3Lem85TwoGap1)
    (g4 : W3Lem85TwoGap4)
    (h : Nat.card S = 2 ∧ ∃ m n : ℕ,
      (IsSpGp (X ⧸ Subgroup.center X) m n ∧
        ∀ s ∈ S, s ≠ 1 → IsSymplecticTransvection X m n s) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) m n ∧ ∀ s ∈ S, s ≠ 1 → IsUnitaryTransvection X m n s) ∨
      IsOrthGp (X ⧸ Subgroup.center X) m n ∨ IsL2WrSymGp (X ⧸ Subgroup.center X) n m) :
    BarConcl X := by
  obtain ⟨hS2, m, n, ⟨hSp, -⟩ | ⟨hPSU, hroot⟩ | hOrth | hWr⟩ := h
  · obtain ⟨k, hk, -⟩ := id hSp
    rcases Nat.lt_or_ge 3 m with hm | hm
    · exact ⟨m, n, hm, Or.inl hSp⟩
    · have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · have h0 : m = 0 := by omega
        subst h0
        have hbot := eq_bot_of_subsingleton_quot hF.situation (subsingleton_of_isSpGp_zero hSp)
        rw [hbot] at hS2
        simp at hS2
      · have h2 : m = 2 := by omega
        subst h2
        exact (false_of_isL2Gp hF (isL2Gp_of_isSpGp_two hSp)).elim
  · obtain ⟨h3, -⟩ := three_le_of_isPSUGp hPSU
    rcases Nat.lt_or_ge 3 m with hm | hm
    · exact ⟨m, n, hm, Or.inr hPSU⟩
    · have h3' : m = 3 := by omega
      subst h3'
      exact (false_of_isPSUGp_three hF g1 hPSU hroot).elim
  · exact (g4 X S hF.situation hS2 (Or.inl ⟨m, n, hOrth⟩) (hF.central hS2)).elim
  · rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · have hbot := eq_bot_of_subsingleton_quot hF.situation
          (subsingleton_of_isL2WrSymGp_zero hWr)
        rw [hbot] at hS2
        simp at hS2
      · exact (false_of_isL2Gp hF (isL2Gp_of_isL2WrSymGp_one hWr)).elim
    · exact (g4 X S hF.situation hS2 (Or.inr ⟨n, m, hm, hWr⟩) (hF.central hS2)).elim

theorem false_of_alt6 (hF : BarFacts X S A Z₁ r) (g6 : W3Lem85TwoGap6)
    (h : Nat.card S = 2 ∧ IsThreeCoverOrth6Minus X) : False :=
  g6 X S hF.situation h.1 h.2 (hF.central h.1)

end CFSG.LocalAnalysis.WeakClosure81

end
